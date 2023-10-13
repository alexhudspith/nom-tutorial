//! Example crate demonstrating how to use nom to parse `/proc/mounts`.
//! Browse crates.io for sys-mount, proc-mounts, and libmount for more stable, usable crates.

use std::fs::File;
// BufRead needed for line-by-line reading of BufReader
use std::io::{self, BufRead, BufReader, Lines};

/// Type-erased errors.
// Must implement Error to satisfy ? syntax; Send + Sync for threads
pub type BoxError = Box<dyn std::error::Error + Send + Sync>;

/// Describes a mounted filesystem, see `man 8 mount` for more details.
#[derive(Clone, Default, Debug)]
pub struct Mount {
    /// The device from which the filesystem is mounted, e.g. /dev/sda1
    pub device: String,
    /// Where in the root filesystem the device is mounted, e.g. /mnt/disk
    pub mount_point: String,
    /// The filesystem type, e.g. ext4
    pub file_system_type: String,
    /// A vector of mount options, e.g. ["ro", "nosuid"]
    /// Note: This could also be implemented as a set (e.g. std::collections::HashSet)
    pub options: Vec<String>,
}

/// Implements `Display` for `Mount` to simulate behavior of Unix mount command.
///
/// # Examples
/// ```
/// use nom_tutorial::Mount;
/// let mount = Mount {
///     device: String::from("/dev/sda1"),
///     mount_point: String::from("/mnt/disk"),
///     file_system_type: String::from("ext4"),
///     options: vec![String::from("ro"), String::from("nosuid")]
/// };
/// assert_eq!(mount.to_string(), "/dev/sda1 on /mnt/disk type ext4 (ro,nosuid)");
/// ```
impl std::fmt::Display for Mount {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} on {} type {} ({})",
            self.device,
            self.mount_point,
            self.file_system_type,
            self.options.join(",")
        )
    }
}

/// An iterator over the mounts contained in `/proc/mounts`.
///
/// See [mounts()] for details.
pub struct Mounts {
    lines: Lines<BufReader<File>>,
}

impl Mounts {
    /// Returns a new Mounts instance (private).
    fn new() -> Result<Mounts, io::Error> {
        let file = File::open("/proc/mounts")?;
        let lines = BufReader::new(file).lines();
        Ok(Mounts { lines })
    }
}

impl Iterator for Mounts {
    type Item = Result<Mount, BoxError>;

    /// Returns the next line in `/proc/mounts` as a [Mount]. If there is a problem
    /// reading or parsing `/proc/mounts`, returns an error. In the case of a parsing
    /// error we use [nom::Err::to_owned()] to allow the returned error to outlive `line`.
    fn next(&mut self) -> Option<Self::Item> {
        match self.lines.next() {
            Some(line) => match line {
                Ok(line) => match parsers::parse_line(&line[..]) {
                    Ok( (_, m) ) => Some(Ok(m)),
                    Err(e) => Some(Err(e.to_owned().into()))
                },
                Err(e) => Some(Err(e.into()))
            },
            None => None
        }
    }
}

// Encapsulate individual nom parsers in a private submodule. The inner pub function
// [parsers::parse_line()] can be called by code within this module, but not by users
// of our crate.
mod parsers {
    use super::Mount;
    use nom::branch::alt;
    use nom::bytes::complete::{escaped_transform, is_not, tag};
    use nom::character::complete::{char, space0, space1};
    use nom::combinator::{all_consuming, map_parser, recognize, value};
    use nom::multi::separated_list;
    use nom::sequence::tuple;
    use nom::IResult;

    type NomError<I> = nom::Err<(I, nom::error::ErrorKind)>;

    #[inline(always)]
    fn nom_parse_error<I>(input: I, kind: nom::error::ErrorKind) -> NomError<I> {
        nom::Err::Error((input, kind))
    }

    /// Extracts a string that does not contain whitespace (space or tab). Anything else goes.
    fn not_whitespace(i: &str) -> IResult<&str, &str> {
        is_not(" \t")(i)
    }

    /// Replaces the sequence 040 with a space.
    fn escaped_space(i: &str) -> IResult<&str, &str> {
        value(" ", tag("040"))(i)
    }

    /// Replaces the escaped sequence \ with a \. The inner parser `nom::character::complete::char`
    /// returns a `char` instead of a `&str`, so we wrap it in a `nom::combinator::recognize`, which
    /// returns that `char` as an `&str` if the inner parser succeeds, and returns an error if the
    /// inner parser fails.
    fn escaped_backslash(i: &str) -> IResult<&str, &str> {
        recognize(char('\\'))(i)
    }

    /// Replaces all instances of \040 in a string with a space.
    /// Replaces \\ with a \.
    fn transform_escaped(i: &str) -> IResult<&str, String> {
        escaped_transform(
            is_not("\\"), '\\', alt((escaped_backslash, escaped_space))
        )(i)
    }

    /// Parses the options of a mount into a comma separated vector of strings. The options string
    /// is terminated by a whitespace. Here we use `nom::combinator::map_parser` to extract the full
    /// whitespace-terminated options string and then pass it in to `transform_escaped` to process
    /// escaped characters. Then the transformed string is split into a comma-delimited vector of
    /// strings by `nom::multi::separated_list`.
    fn mount_opts(i: &str) -> IResult<&str, Vec<String>> {
        separated_list(
            char(','),
            map_parser(is_not(", \t"), transform_escaped)
        )(i)
    }

    /// Parses a line from `/proc/mounts` into a Mount struct. This is perhaps the most
    /// complex-looking parser, but it is actually one of the simplest because we build upon each of
    /// the parsers defined above. Let's break it down parser by parser:
    /// `nom::combinator::all_consuming` generates an error if there is any leftover input. This
    /// will force nom to generate an error if there is unexpected input at the end of a line in
    /// `/proc/mounts`, for example:
    /// ```ignore
    /// /dev/sda1 /mnt/disk ext4 defaults 0 0 this_last_part_shouldn't_be_here
    /// ```
    ///
    /// `nom::sequence::tuple` generates a `Result<Ok(remaining_input: &str, output_tuple), Error>`.
    /// Although it looks complicated, we can very easily destructure that tuple. Each sub/inner
    /// parser we pass to `nom::sequence::tuple` generates its own element within the tuple. We can
    /// ignore the whitespace by matching it with `_` and destructure the other elements of the
    /// tuple as the variables we are interested in such as `device`, `mount_point`, etc. If
    /// everything goes as planned we return a new instance of the mount `Mount` structure populated
    /// with the variables we destructured from the tuple.
    /// ```ignore
    /// let (device, _, mount_point /*, ...*/) = ("/dev/sda1", " ", "/mnt/disk" /*, ...*/);
    ///                                           /* ^- tuple returned by all_consuming(tuple()) */
    /// let mount = Mount {
    ///     device: device.to_string(), mount_point: mount_point.to_string() /*, ...*/
    /// };
    /// ```
    pub fn parse_line(i: &str) -> IResult<&str, Mount> {
        let mut parser = all_consuming(tuple((
            map_parser(not_whitespace, transform_escaped), // device
            space1,
            map_parser(not_whitespace, transform_escaped), // mount_point
            space1,
            not_whitespace, // file_system_type
            space1,
            mount_opts, // options
            space1,
            char('0'),
            space1,
            char('0'),
            space0,
        )));

        match parser(i) {
            Ok((i, (device, _, mount_point, _, file_system_type, _, options, ..))) => {
                let file_system_type = file_system_type.to_string();
                Ok((i, Mount { device, mount_point, file_system_type, options }))
            }
            Err(e) => Err(e),
        }
    }

    /// Alternative version of `parse_line()` above that performs the same function using
    /// a different style. Rather than parsing the entire line at once with one big
    /// `nom::sequence::tuple` we break the parsing up into multiple separate statements.
    /// Each statement runs a parser that returns an `Ok(remaining_input, value)`. At the end of
    /// each statement we have the `?` operator, which unwraps the result and returns early with an
    /// error if parsing failed. The remaining input from each parser is used as the input of each
    /// subsequent parser. Values are assigned to temporary variables that are used to construct a
    /// `Mount` object at the end of the function. Values that are not needed are discarded by
    /// assigning to `_`.
    #[allow(unused)]
    pub fn parse_line_alt(i: &str) -> IResult<&str, Mount> {
        let (i, device) = map_parser(not_whitespace, transform_escaped)(i)?; // device
        let (i, _) = space1(i)?;
        let (i, mount_point) = map_parser(not_whitespace, transform_escaped)(i)?; // mount_point
        let (i, _) = space1(i)?;
        let (i, file_system_type) = not_whitespace(i)?; // file_system_type
        let (i, _) = space1(i)?;
        let (i, options) = mount_opts(i)?; // options
        let (i, _) = all_consuming(
            tuple((space1, char('0'), space1, char('0'), space0))
        )(i)?;

        let file_system_type = file_system_type.to_string();
        Ok((i, Mount { device, mount_point, file_system_type, options }))
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use nom::error::ErrorKind;

        // Extracts a string that does not contain whitespace, i.e. comma or tab.
        #[test]
        fn test_not_whitespace() {
            assert_eq!(not_whitespace("abcd efg"), Ok((" efg", "abcd")));
            assert_eq!(not_whitespace("abcd\tefg"), Ok(("\tefg", "abcd")));
            let error = nom_parse_error(" abcdefg", ErrorKind::IsNot);
            assert_eq!(not_whitespace(" abcdefg"), Err(error));
        }

        // Converts 040 to a space. Does not actually recognize a literal space.
        #[test]
        fn test_escaped_space() {
            assert_eq!(escaped_space("040"), Ok(("", " ")));
            let error = nom_parse_error(" ", ErrorKind::Tag);
            assert_eq!(escaped_space(" "), Err(error));
        }

        // Converts `char` \ to `&str` \.
        #[test]
        fn test_escaped_backslash() {
            assert_eq!(escaped_backslash("\\"), Ok(("", "\\")));
            let error = nom_parse_error("not a backslash", ErrorKind::Char);
            assert_eq!(escaped_backslash("not a backslash"), Err(error));
        }

        // Recognizes each escape sequence and transforms it to the escaped literal.
        // For example, each \040 is transformed into a space.
        #[test]
        fn test_transform_escaped() {
            assert_eq!(
                transform_escaped("abc\\040def\\\\g\\040h"),
                Ok(("", String::from("abc def\\g h")))
            );
            let error = nom_parse_error("bad", ErrorKind::Tag);
            assert_eq!(transform_escaped("\\bad"), Err(error));
        }

        // Parses a comma separated list of mount options, which might contain spaces.
        #[test]
        fn test_mount_opts() {
            assert_eq!(
                mount_opts("a,bc,d\\040e"),
                Ok(("", vec![
                    "a".to_string(),
                    "bc".to_string(),
                    "d e".to_string()
                ]))
            );
        }

        // Parses a line from /proc/mounts
        #[test]
        fn test_parse_line() {
            let mount1 = Mount {
                device: "device".to_string(),
                mount_point: "mount_point".to_string(),
                file_system_type: "file_system_type".to_string(),
                options: vec![
                    "options".to_string(),
                    "a".to_string(),
                    "b=c".to_string(),
                    "d e".to_string(),
                ],
            };
            let (_, mount2) =
                parse_line("device mount_point file_system_type options,a,b=c,d\\040e 0 0")
                    .unwrap();
            assert_eq!(mount1.device, mount2.device);
            assert_eq!(mount1.mount_point, mount2.mount_point);
            assert_eq!(mount1.file_system_type, mount2.file_system_type);
            assert_eq!(mount1.options, mount2.options);
        }

        // Parses a line from /proc/mounts
        #[test]
        fn test_parse_line_alt() {
            let mount1 = Mount {
                device: "device".to_string(),
                mount_point: "mount_point".to_string(),
                file_system_type: "file_system_type".to_string(),
                options: vec![
                    "options".to_string(),
                    "a".to_string(),
                    "b=c".to_string(),
                    "d e".to_string(),
                ],
            };
            let (_, mount2) =
                parse_line_alt("device mount_point file_system_type options,a,b=c,d\\040e 0 0")
                    .unwrap();
            assert_eq!(mount1.device, mount2.device);
            assert_eq!(mount1.mount_point, mount2.mount_point);
            assert_eq!(mount1.file_system_type, mount2.file_system_type);
            assert_eq!(mount1.options, mount2.options);
        }
    }
}

/// Returns an iterator over the mounts contained in `/proc/mounts`.
///
/// Instantiation may fail if `/proc/mounts` does not exist or you do not have access to read it.
/// You can access each individual mount through [Iterator::next()].
///
/// # Examples
/// ```
/// use nom_tutorial;
/// for mount in nom_tutorial::mounts().unwrap() {
///   println!("{}", mount.unwrap());
/// }
///
/// let mut iter = nom_tutorial::mounts().expect("Couldn't access /proc/mounts.");
/// match iter.next() {
///     Some(m) => match m {
///         Ok(m) => eprintln!("Here is a mounted filesystem: {}", m),
///         Err(e) => eprintln!("There was an error parsing the next line in /proc/mounts: {}", e)
///     },
///     None => eprintln!("There are no mounted filesystems.")
/// }
/// ```
pub fn mounts() -> Result<Mounts, io::Error> {
    Mounts::new()
}

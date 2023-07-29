my_string : String { "hi" }

my_string_with_escaped_quote : String { "here is a quote: \" " }

my_string_with_escaped_backslash : String { "here is a backslash: \\ " }

both : String {
  "here is a backslash in quotes: \"\\\" "
}

type TwoStrings { MkTwoStrings String String }

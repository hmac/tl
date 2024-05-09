["case" "let"] @keyword
; TODO: "type" "test"

(int) @number
(string) @string
(char) @char

[":" "->"] @operator

(func_decl
  name: (l_ident) @function)

(type_name) @type
(var_type) @type
(app_type) @type
(func_type) @type

(ctor) @constructor

(comment) @comment

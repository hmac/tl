["case" "let"] @keyword
; TODO: "type" "test"

(int) @number
(string) @string
(char) @char

[":" "->"] @operator

(func_decl
  name: (l_ident) @function)

(type_decl
  name: (u_ident) @type)
(type_decl_ctor name: (u_ident) @type.enum.variant)

(type_name) @type
(var_type) @type.parameter
(app_type) @type
(func_type) @type

(ctor) @constructor

(comment) @comment

(nullary_ctor_pattern) @constructor
(ctor_pattern (u_ident) @constructor)

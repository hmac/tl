const parens = (...rule) => seq('(', ...rule, ')');
const brackets = (...rule) => seq('[', ...rule, ']');
const sep_by1 = (separator, ...rule) => seq(...rule, repeat(seq(separator, ...rule)), optional(separator));
const sep_by = (separator, ...rule) => optional(sep_by1(separator, ...rule));

module.exports = grammar({
  name: 'tl',

  extras: $ => [
    /\s/,
    $.comment
  ],

  rules: {
    source_file: $ => repeat($._decl),

    comment: $ => /\/\/[^\n]+/,

    _decl: $ => choice(
      $.func_decl
    ),

    func_decl: $ => seq(
      field("name", $.l_ident),
      ":",
      field("type", $._type),
      "{",
      field("body", $._expr),
      "}"
    ),

    _type: $ => choice(
      $._atomic_type,
      $.app_type,
      $.func_type,
    ),

    // Helpers for parsing types
    // We separate "atomic" types from functions and applications to avoid left-recursion.
    _atomic_type: $ => choice(
      $.type_name,
      $.var_type,
      parens($._type)
    ),
    type_name: $ => $.u_ident,
    var_type: $ => $.l_ident,
    app_type: $ => prec.left(2,
      seq(
        field("head", $._atomic_type),
        repeat1($._atomic_type)
      )
    ),
    func_type: $ => prec.right(1,
      seq(
        $._type,
        "->",
        $._type
      )
    ),
    _expr: $ => choice(
      $._expr_except_var,
      $.func_or_app
    ),

    // Separate var from other expressions in order to parse applications and functions correctly.
    // TODO: explain this properly
    _expr_except_var: $ => prec(3,
        choice(
        $.ctor,
        $.int,
        $.string,
        $.char,
        $.tuple,
        $.list,
        $.case,
        $.let,
        parens($._expr)
      )
    ),

    ctor: $ => $.u_ident,
    int: $ => /[0-9]+/,
    string: $ => /"(\\[\\"]|[^\\"]*)"/,
    char: $ => /'[^']'/,
    tuple: $ => parens(
      choice(
        ",",
        sep_by(",", $._expr)
      ),
    ),
    list: $ => brackets(
      sep_by(",", $._expr)
    ),
    case: $ => seq(
      "case",
      $._expr,
      "{",
      sep_by(",", $.branch),
      "}"
    ),
    branch: $ => seq(
      field("pattern", $._pattern),
      "->",
      field("rhs", $._expr)
    ),

    _pattern: $ => choice(
      $.ctor_pattern,
      $._atomic_pattern
      // TODO: other patterns
    ),
    _atomic_pattern: $ => choice(
      $.nullary_ctor_pattern,
      $.var_pattern,
      $.int_pattern,
      $.list_pattern,
      $.tuple_pattern,
    ),
    int_pattern: $ => $.int,
    var_pattern: $ => $.l_ident,
    nullary_ctor_pattern: $ => $.u_ident,
    ctor_pattern: $ => seq(
      $.u_ident,
      repeat1($._atomic_pattern)
    ),
    list_pattern: $ => choice(
      brackets($.list_pattern_rest),
      brackets(
        seq(
          sep_by(",", $._pattern),
          optional(seq(",", $.list_pattern_rest)),
        )
      )
    ),
    list_pattern_rest: $ => seq("..", $.l_ident),
    tuple_pattern: $ => parens(sep_by(",", $._pattern)),

    func_or_app: $ => prec.right(1,
      seq(
        $.func_params,
        optional(
          seq(
            "->",
            field("body", $._expr)
          )
        )
      )
    ),
    func_params: $ => prec.left(repeat1($.l_ident)),
    app: $ => prec.left(1,
      seq(
        choice($._expr_except_var, $.app),
        $._expr_except_var
      )
    ),
    let: $ => seq(
      "let",
      repeat1($.let_bind),
      "{",
      field("body", $._expr),
      "}"
    ),
    let_bind: $ =>  seq(
      $.l_ident,
      "=",
      $._expr
    ),

    l_ident: $ => /[a-z_][a-zA-Z0-9_]*/,
    u_ident: $ => /[A-Z_][a-zA-Z0-9_]*/
  }
});


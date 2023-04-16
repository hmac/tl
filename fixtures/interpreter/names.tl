// Different types of function and type name

type ManyCapitalLetters { MkTheType }

type _LeadingUnderscore { _AndAgain, In_The_Middle }

func_with_underscores : ManyCapitalLetters { MkTheType }

func123 : Int { 1 }

_lead_underscore_func_123 : Int { 2 }

lowercaseWithCapitals : Int { 3 }

wildcard : _LeadingUnderscore -> _LeadingUnderscore {
  l -> match l {
    _In_The_Middle -> _AndAgain,
    _ -> In_The_Middle
  }
}

main : Int { 1 }
---
1

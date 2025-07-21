import PosixSubmatching.Regex

open Regex

/-- Implicit coercion to convert characters to regexes -/
instance : Coe Char (Regex Char) where
  coe := char

-- (a*)* · b*
def r₁ : Regex Char := (group "0" [] (star 'a')).star.mul (star 'b')
#eval r₁.captures "bb".toList
#eval r₁.captures "aabb".toList

-- (a + aa)*
def r₂ : Regex Char := (group "0" [] (plus 'a' (mul 'a' 'a'))).star
#eval r₂.captures []
#eval r₂.captures "aaa".toList
#eval r₂.captures "aaaa".toList

-- (a + ab)(b + ε)
def r₃ : Regex Char := (group "0" [] (plus 'a' (mul 'a' 'b'))).mul (group "1" [] (plus 'b' epsilon))
#eval r₃.captures "ab".toList
#eval r₃.captures "abb".toList
#eval r₃.captures "a".toList

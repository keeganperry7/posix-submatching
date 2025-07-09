import PosixSubmatching.Regex
import PosixSubmatching.Value

open Regex

/-- Implicit coercion to convert characters to regexes -/
instance : Coe Char (Regex Char) where
  coe := char

-- (a*)* · b*
def r₁ : Regex Char := (group "0" [] (star 'a')).star.mul (star 'b')
#guard r₁.captures "bb".toList = r₁.captures' "bb".toList
#guard r₁.captures "aabb".toList = r₁.captures' "aabb".toList

-- (a + aa)*
def r₂ : Regex Char := (group "0" [] (plus 'a' (mul 'a' 'a'))).star
#guard r₂.captures [] = r₂.captures' []
#guard r₂.captures "aaa".toList = r₂.captures' "aaa".toList
#guard r₂.captures "aaaa".toList = r₂.captures' "aaaa".toList

-- (a + ab)(b + ε)
def r₃ : Regex Char := (group "0" [] (plus 'a' (mul 'a' 'b'))).mul (group "1" [] (plus 'b' epsilon))
#guard r₃.captures "ab".toList = r₃.captures' "ab".toList
#guard r₃.captures "abb".toList = r₃.captures' "abb".toList
#guard r₃.captures "a".toList = r₃.captures' "a".toList

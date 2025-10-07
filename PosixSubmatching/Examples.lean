import PosixSubmatching.Regex

open Regex

/-- Implicit coercion to convert characters to regexes -/
instance : Coe Char (Regex Char) where
  coe := char

-- (a*)* · b*
def r₁ : Regex Char := (group 0 [] (star 'a')).star.mul (star 'b')
#guard r₁.captures "bb".toList = some []
#guard r₁.captures "aabb".toList = some [(0, "aa".toList)]

-- (a + aa)*
def r₂ : Regex Char := (group 0 [] (plus 'a' (mul 'a' 'a'))).star
#guard r₂.captures [] = some []
#guard r₂.captures "aaa".toList = some [(0, ['a', 'a']), (0, ['a'])]
#guard r₂.captures "aaaa".toList = some [(0, ['a', 'a']), (0, ['a', 'a'])]

-- (a + ab)(b + ε)
def r₃ : Regex Char := (group 0 [] (plus 'a' (mul 'a' 'b'))).mul (group 1 [] (plus 'b' epsilon))
#guard r₃.captures "ab".toList = some [(0, ['a', 'b']), (1, [])]
#guard r₃.captures "abb".toList = some [(0, ['a', 'b']), (1, ['b'])]
#guard r₃.captures "a".toList = some [(0, ['a']), (1, [])]

#guard (captures (group 1 [] (not (char 'b'))) "a".toList) = Option.some  [(1, "a".toList)]

#guard (captures (group 1 [] (not (mul (char 'a') (char 'b')))) "abc".toList) = Option.some [(1, "abc".toList)]

#guard captures (group 1 [] (not (not (char 'b')))) "b".toList = Option.some [(1, "b".toList)]

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

def r₄ : Regex Char := not (group 1 [] (char 'a'))
#eval r₄.captures' "bb".toList
#eval r₄.captures'' "bb".toList

def r₅ : Regex Char := not (mul (group 1 [] (char 'a')) (group 2 [] (char 'b')))
#eval r₅.derivs "abc".toList
#eval r₅.captures' "abc".toList
#eval r₅.captures'' "abc".toList

def r₆ : Regex Char := not (not (group 1 [] (char 'a')))
#eval r₆.derivs "a".toList
#eval r₆.captures' "a".toList
#eval r₆.captures'' "a".toList

def r₇ : Regex Char := not (plus (not (group 1 [] (char 'a'))) (not (group 2 [] (char 'a'))))
#eval r₇.derivs "a".toList
#eval r₇.captures' "a".toList
#eval r₇.captures'' "a".toList

def r₈ : Regex Char := not (and (group 1 [] (mul (char 'a') (char 'b'))) (group 2 [] (char 'a')))
#eval r₈.captures' "ab".toList
#eval r₈.captures'' "ab".toList

def r₉ : Regex Char := not (mul (group 1 [] (char 'a')) (mul (group 2 [] (char 'b')) (group 3 [] (char 'c'))))
#eval r₉.captures'' "abcd".toList


#guard (captures (group 1 [] (not (char 'b'))) "a".toList) = Option.some  [(1, "a".toList)]

#guard (captures (group 1 [] (not (mul (char 'a') (char 'b')))) "abc".toList) = Option.some [(1, "abc".toList)]

#guard captures (group 1 [] (not (not (char 'b')))) "b".toList = Option.some [(1, "b".toList)]

#guard captures
  (group 1 [] (and (char 'b') (char 'b')))
  "b".toList
  = Option.some [(1, "b".toList)]

#guard captures
  (group 1 [] (and (not (char 'a')) (char 'b')))
  "b".toList
  = Option.some [(1, "b".toList)]

#guard captures
  (group 1 [] (and (not (char 'a')) (not (char 'c'))))
  "b".toList
  = Option.some [(1, "b".toList)]

#guard captures
  (group 1 [] (and (not (char 'a')) (not (char 'c'))))
  "bb".toList
  = Option.some [(1, "bb".toList)]

#guard captures
  (and (group 1 [] (not (char 'a'))) (not (char 'c')))
  "bb".toList
  = Option.some [(1, "bb".toList)]

#guard captures
  (and (group 1 [] (not (char 'a'))) (star (char 'b')))
  "bb".toList
  = Option.some [(1, "bb".toList)]

#guard captures
  (and (group 1 [] (not (char 'a'))) (star (char 'c')))
  "bb".toList
  = Option.none

#guard captures
  (group 1 [] (and (not (char 'a')) (star (char 'c'))))
  "bb".toList
  = Option.none

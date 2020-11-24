
import Data.Vect

total
append : Vect n a -> Vect m a -> Vect (n+m) a
append [] ys = ys
append (x::xs) ys = x :: append xs ys

total
lappend: List a -> List a -> List a
lappend [] ys = ys
lappend (x::xs) ys = x :: lappend xs ys

-- Curry-Howard : propositions as types, proofs are terms/programs.

--sumLengths : (n:Nat) -> (m:Nat) -> (xs : List a) -> length []
-- sumLengths = PROOF
 
total
appendLengths : (xs : List a) -> (ys : List a) ->  
  length (lappend xs ys) = length xs + length ys
appendLengths [] _ = Refl
  -- The above follows this chain of inference:
  --    length (lappend [] ys) = length [] + length ys # Subst [] for xs
  --    length ys = length [] + length ys             # Expand lappend base case
  --    length ys = 0 + length ys                   # Length [] = 0
  --    length ys = length ys                       # Adding 0 doesn't change
appendLengths (x::xs) ys = 
  rewrite appendLengths xs ys in
  Refl
  -- Chain of inference for inductive case:
  --    length (lappend (x::xs) ys) = length (x::xs) + length ys # Subst xs
  --    length (x :: lappend xs ys) = length (x::xs) + length ys # Expand lappend
  --    length (x :: lappend xs ys) = (S (length xs)) + length ys # length cons->S
  --    length (x :: lappend xs ys) = S (length xs + length ys) # Associative+
  --    S (length (lappend xs ys)) = S (length xs + length ys) # length cons->S
  --    length (lappend xs ys) = (length xs + length ys) # Inductive hypothesis
  --    QED.

total
emplist : 5 = 5
emplist = Refl

-- Reverse a list without using append (accumulator argument)

revv : List a -> List a -> List a
revv accum [] = accum
revv accum (x::xs) = revv (x::accum) xs

-- revvLength : (xs: List a) -> (ys: List a) -> 
--    length (revv xs ys) = length xs + length ys
-- revvLength accum [] = rewrite plusZeroRightNeutral (length accum) in Refl
-- revvLength accum (x::xs) = 
--   rewrite plusSuccRightSucc (length accum) (length xs) in ?x
--  rewrite revvLength accum xs in ?x

-- rev1 : List a -> List a
-- rev1 xs = revv [] xs

-- rev1Length : (xs: List a) -> length xs = length (rev1 xs)
-- rev1Length xs =
--   rewrite revvLength [] xs in
--   Refl



-- Vector version

-- revvv : Vect n a -> Vect m a -> Vect (n+m) a
-- revvv [] ys = ys
-- revvv (x::xs) ys = revvv xs (x::ys)




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

-- Reverse a list without using append (accumulator argument)

total
revHelper : List a -> List a -> List a
revHelper [] accum = accum
revHelper (x::xs) accum = revHelper xs (x::accum)

total
lengthRevHelper : (xs: List a) -> (accum: List a) -> length (revHelper xs accum) = length xs + length accum
lengthRevHelper [] _ = Refl
lengthRevHelper (x::xs) accum =
  rewrite lengthRevHelper xs (x::accum) in 
  rewrite plusSuccRightSucc (length xs) (length accum) in
  Refl

-- Top-level invocation of reverse, using helper

total
myRev : List a -> List a
myRev xs = revHelper xs [] 

total
lengthMyRev : (xs: List a) -> length (myRev xs) = length xs
lengthMyRev xs = 
  rewrite lengthRevHelper xs [] in 
  rewrite plusZeroRightNeutral (length xs) in
  Refl

-- Reverse a list using append (so we'll rely on our implementation and proof of lengths)

total
myRevApp : List a -> List a
myRevApp [] = []
myRevApp (x::xs) = lappend (myRevApp xs) [x]

-- Appending a single element to the end increases length by 1.
total
snocLengthSucc : (xs : List a) -> (y: a) -> length (lappend xs [y]) = S (length xs)
snocLengthSucc [] x = Refl
snocLengthSucc (x::xs) y =
  rewrite snocLengthSucc xs y in Refl

-- Now we can prove that append-based reverse preserves length.
total
lengthMyRevApp : (xs: List a) -> length (myRevApp xs) = length xs
lengthMyRevApp [] = Refl
lengthMyRevApp (x::xs) =
  rewrite snocLengthSucc (myRevApp xs) x in 
  rewrite lengthMyRevApp xs in Refl

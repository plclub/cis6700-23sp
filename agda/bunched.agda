module Bunched where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_ ;  z≤n ; s≤s ; ≤-pred )

open import Data.List using (List;_∷_; [])

-- Some types
data Ty : Set where
  Unit Void  : Ty
  And Or Imp : Ty -> Ty -> Ty

-- Bunched contexts 

data B : Set where

  ` : Ty -> B

  one  : B 

  _**_ : B -> B -> B

  zero : B

  _++_ : B -> B -> B

-- An "index" is a pointer to a type in a bunched context
mutual 

  data _∋_ : B → Ty → Set where

    here : ∀ {A}
      → ` A ∋ A

    mult1 : ∀ {L1 L2}{A}

      → L1 ∋ A
      ---------
      → (L1 ** L2) ∋ A

    mult2 : ∀ {L1 L2}{A}

      → L2 ∋ A
      ---------
      → (L1 ** L2) ∋ A

    add1 : ∀ {L1 L2 : B}{A}
      → L1 ∋ A
      ---------
      → (L1 ++ L2) ∋ A

    add2 : ∀ {L1 L2 : B}{A}
      → L2 ∋ A
      ---------
      → (L1 ++ L2) ∋ A


-- equality for bunched context

data _==_ : B -> B -> Set where
  
  mulid1 : ∀ { b } -> ( one ** b ) == b

  mulid2 : ∀ { b } -> ( b ** one ) == b

  mulc : ∀ b1 b2 b1' b2' 
       -> b1 == b1' -> b2 == b2' -> ((b1 ** b2) == (b1' ** b2'))

  mulassoc  : ∀ { b1 b2 b3 } -> ( b1 ** (b2 ** b3) ) == ((b1 ** b2) ** b3)

-- transform references from LHS context to RHS context

shift : ∀ { b1 b2 A } -> b1 == b2 -> b1 ∋ A -> b2 ∋ A
shift mulid1 (mult2 v) = v
shift mulid2 (mult1 v) = v
shift (mulc b1 b2 b1' b2' pf pf₁) v = {!!}
shift mulassoc v = {!!}


-- A hole is a reference to a bunch in a context

mutual 

  data _[·]  : B → Set where

    here  : ∀ {b}
      → b [·] 

    mult1 : ∀ {b1 b2 : B}{b : B}
      → b1 [·]
      -----------
      → (b1 ** b2) [·]

    mult2 : ∀ {b1 b2 : B}{b : B}
      → b2 [·]
      -----------
      → (b1 ** b2) [·]

    add1 : ∀ {b1 b2 : B}{b : B}
      → b1 [·]
      -----------
      → (b1 ++ b2) [·]

    add2 : ∀ {b1 b2 : B}{b : B}
      → b2 [·]
      -----------
      → (b1 ++ b2) [·]

_[_] : ∀ {Γ} -> Γ [·] -> B -> B
here [ b ] =  b
mult1 {b1}{b2} Γ [ b ] = ( Γ [ b ] ) ** b2
mult2 {b1}{b2} Γ [ b ] = b1 ** (Γ [ b ])
add1 {b1}{b2} Γ [ b ] =  ( Γ [ b ] ) ++ b2 
add2 {b1}{b2} Γ [ b ] =  b1 ++ (Γ [ b ])

data _⊢_ : B -> Ty -> Set where
  
  -- Id  (variable rule)
  `_ : ∀ {A} -> ` A ⊢ A

  -- Conversion
  -- This is the heavy lifting (!!!)
  ◂  : ∀ {Γ Δ A} -> Γ ⊢ A -> Γ == Δ -> Δ ⊢ A 

  -- Weakening
  W : ∀ {Δ}{Γ : Δ [·]}{b : B}{A : Ty} 
    -> ( Γ [ b ] ) ⊢ A -> ( Γ [ b ** b ] ) ⊢ A 

  -- Contraction
  C : ∀ {Δ}{Γ : Δ [·]}{b A} -> ( Γ [ b ** b ] ) ⊢ A -> ( Γ [ b ] ) ⊢ A
  
  -- unit intro
  1-I : zero ⊢ Unit
   
  -- unit elim 
  1-E : ∀ {A}{Δ Δ₁ : B}{Γ : Δ₁ [·]} -> (Γ [ zero ]) ⊢ A -> (Δ ⊢ Unit) -> (Γ [ Δ ]) ⊢ A 

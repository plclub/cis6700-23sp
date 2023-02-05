{-# OPTIONS --without-K --sized-types #-}

module DeBruijn where

-- This module defines a data type for lambda calculus expressions
-- represented by de Bruijn indices and a substitution operations. 
-- It refers to N.G. de Bruijn's article
--  "Lambda Calculus notation with nameless dummies,
--   A tool for automatic formula manipulation with application 
--   to the Church-Rosser Theorem"
-- In order to interpolate the original definitions to those 
-- shown in PFLA.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Codata.Stream 
  using (Stream; _∷_; lookup; map; zipWith; tail; nats)
open import Codata.Thunk using (force)
open import Size

-- Syntax: Here is the definition of "namefree" expressions
-- that we work with in this file.

infix  8  #_
infix  6  ƛ_
infixl 7  _·_

-- NF stands for "namefree"
data NF : Set where
  #_  : ℕ -> NF          -- variable (index)
  ƛ_  : NF -> NF         -- abstraction
  _·_ : NF -> NF -> NF   -- application

{- 

Take a moment to compare this definition with the one shown in
Section 5 of de Bruijn's article.

We make a few changes from de Bruijn's definition:

    1. We start counting from 0 instead of 1
    2. We drop constants and primitive function symbols
    3. We use single application (M N) instead of 
       multi-application with a special "A" symbol
       i.e. A( M1 , M2 , ... )
    4. Instead of capital greek letters for lambda 
       expressions (Σ, Ω), we use M, N, P as metavars.
-}


-- Here are some Church numerals expressed in this notation.

twoᶜ : NF
twoᶜ =  ƛ ƛ (# 1 · (# 1 · # 0))

fourᶜ : NF
fourᶜ = ƛ ƛ (# 1 · (# 1 · (# 1 · (# 1 · # 0))))

plusᶜ : NF
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

2+2ᶜ : NF
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ

------------------------------
-- Substitution (Section 6)

module DeBruijn where

   {- 

   N. G. de Bruijn represents substitutions using an infinite
   list of lambda terms, ordered right-to-left. This corresponds
   to replacing variable #i with the term at position i in the
   list. (Also, recall that indexing starts at 1 for de Bruijn).
   
   We can model this in Agda using a *coinductive stream* of
   namefree terms. Agda's streams are written left-to-right and
   indexing starts at 0.  (See Codata.Stream from the standard
   library for more details.)

   -}

   Substitution = Stream NF ∞

   -- For example, the identity substitution replaces the index
   -- at position i with a variable with the same index. If we
   -- apply this substitution to a namefree term, it shouldn't
   -- change anything.

   σ_id : Substitution
   σ_id = map #_ nats     -- nats is the stream  0 ∷ 1 ∷ 2 ∷ ...

   -- And here is an increment substitution that adds one to each
   -- index We want this substitution to behave like
   -- weakening. It should increment all of the free variables of
   -- the term and leave the bound ones alone.
   σ_incr = map (λ i -> # (suc i)) nats

   -- The substitution function in de Brujn's paper is written as 
   --
   --     S( ... <Σ₃>, <Σ₂>, <Σ₁>; Ω ) 
   --
   -- In Agda, we'll write it as 
   -- 
   --     subst σ M

   mutual 
     {-# TERMINATING #-}
     subst : Substitution -> NF -> NF
     -- (iii)
     subst σ (L · M) = subst σ L · subst σ M
     -- (iv)
     subst σ (# x) = lookup x σ 
     -- (v)
     subst σ (ƛ N) = ƛ subst (exts σ) N

     exts : Substitution -> Substitution
     exts σ = (# 0) ∷ λ where .force -> map (subst σ_incr) σ

     {- In the last case, if Σ is (... <Σ₃>, <Σ₂>, <Σ₁>) then de
     Bruijn says the result is

         S ( ... <Λ₃>, <Λ₂>, <Λ₁>, 1 ; N )

     where each <Λᵢ> is "obtained by adding 1 to every integer
     in <Σᵢ> that refers to a free variable. (Note that these
     terms have also each been shifted over one step in the
     list.)

     With our version, we start the new substitution with 0
     (which corresponds to index 1) and then weaken all of the
     terms that appear in the original substitution.  To do so
     we use the stream's `map` operation with our weakening
     substitution above.

     -}


     test = subst σ_incr (ƛ ( # 2 · # 1 · # 0 · (ƛ # 2 · # 1)))
        -- C-c C-n can normalize this to
        -- ƛ # 3 · # 2 · # 0 · (ƛ # 3 · # 1)

     {-

     However, this definition is not obviously terminating. So 
     Agda rejects it without the annotation. 

     The solution is to build up this definition in two parts.

     First, renaming just replaces indices with other indices, 
     then the increment part of substitution in the lambda case 
     is defined using renaming.

     -}




module Streams where

   -- A renaming is just a stream of natural numbers. We can only 
   -- replace indices by other indices.
   Renaming = Stream ℕ ∞

   ρ_id : Renaming
   ρ_id = nats

   ρ_incr : Renaming
   ρ_incr = map suc nats

   -- We can compute the extended renaming in the lambda-case 
   -- without a recursive call to rename.
   -- Note that The renaming is shifted over because we add 0 to 
   -- the front.
   -- To add 1 to each index in the renaming, we just use 'suc'
   ext : Renaming -> Renaming
   ext ρ = 0 ∷ λ where .force -> map suc ρ

   -- The rename function is a simple structural recursion
   rename : Renaming -> NF -> NF
   rename ρ (# x)    = # (lookup x ρ)
   rename ρ (ƛ M)    = ƛ rename (ext ρ) M
   rename ρ (L · M) = rename ρ L · rename ρ M

   -- Some examples (use C-c C-n to normalize them)
   t1 = rename ρ_id (ƛ ( # 1 · # 0))
   t2 = rename ρ_incr (ƛ ( # 2 · # 1 · # 0 · (ƛ # 2 · # 1)))
      -- ƛ # 3 · # 2 · # 0 · (ƛ # 3 · # 1)

   Substitution = Stream NF ∞

   -- Now to define the extended substitution, we use rename to increment 
   -- all indices in the terms in the substitution.
   exts : Substitution -> Substitution
   exts σ = (# 0) ∷ λ where .force -> map (rename ρ_incr) σ

   -- Substitution is also a simple structural recursion
   subst : Substitution -> NF -> NF
   subst σ (# x) = lookup x σ 
   subst σ (ƛ N) = ƛ subst (exts σ) N
   subst σ (L · M) = subst σ L · subst σ M

   -- We can convert a renaming to a substitution.
   r-to-s : Renaming -> Substitution
   r-to-s ρ = map #_ ρ

   t3 = subst (r-to-s ρ_incr) (ƛ ( # 2 · # 1 · # 0 · (ƛ # 2 · # 1)))
    -- ƛ # 3 · # 2 · # 0 · (ƛ # 3 · # 1)

   -- Single substitution AKA "open": replace index 0 with M, decrement
   -- all other free variables. (Leave bound vars alone.)
   subst-zero : NF -> Substitution
   subst-zero M = M ∷ λ where .force -> (map #_ ρ_id)

   t4 = subst (subst-zero (ƛ # 0)) (# 0 · # 1)
    -- (ƛ # 0) · # 0
   t5 = subst (subst-zero (ƛ # 0)) (ƛ (# 0 · # 1))
    -- ƛ # 0 · (ƛ # 0)
   t6 = subst (subst-zero (ƛ # 0)) (ƛ (# 0 · # 1 · # 2))
    -- ƛ # 0 · (ƛ # 0) · # 1
   t7 = subst (subst-zero (ƛ # 0)) (ƛ ( # 2 · # 1 · # 0 · (ƛ # 2 · # 1)))
    -- ƛ # 1 · (ƛ # 0) · # 0 · (ƛ (ƛ # 0) · # 1)
   

{- Instead of using infinite streams of numbers/terms we can also 
   represent multi-renamings/substitions using functions. 
-}

module Functions where

  Renaming     = ℕ -> ℕ    -- lookup the renaming at an index
  Substitution = ℕ -> NF   -- lookup a substitution at an index

  ρ_id : Renaming 
  ρ_id n = n

  ρ_incr : Renaming 
  ρ_incr = suc

  ext : Renaming -> Renaming
  ext ρ zero = zero            
    -- at index 0 return 0
  ext ρ (suc x) = suc (ρ x)    
    -- everywhere else, add one to old value that was just before this one

  -- The rename function is the same structural recursion
  rename : Renaming -> NF -> NF
  rename ρ (# x)    = # (ρ x)
  rename ρ (ƛ N)    = ƛ rename (ext ρ) N
  rename ρ (L · M) = rename ρ L · rename ρ M

  -- Some examples (use C-c C-n to normalize them)
  t1 = rename ρ_id (ƛ ( # 1 · # 0))
  t2 = rename ρ_incr (ƛ ( # 2 · # 1 · # 0 · (ƛ # 2 · # 1)))
       -- ƛ # 3 · # 2 · # 0 · (ƛ # 3 · # 1)
  
  exts : Substitution -> Substitution
  exts σ zero = # zero               -- at index 0 return # 0
  exts σ (suc n) = rename suc (σ n)  -- everywhere else, increment 
  
   -- Substitution is also a simple structural recursion
  subst : Substitution -> NF -> NF
  subst σ (# x) = σ x 
  subst σ (ƛ N) = ƛ subst (exts σ) N
  subst σ (L · M) = (subst σ L) · (subst σ M)

  subst-zero : NF -> Substitution
  subst-zero M zero = M
  subst-zero M (suc n) = # n

  t4 = subst (subst-zero (ƛ # 0)) (# 0 · # 1)
   -- (ƛ # 0) · # 0
  t5 = subst (subst-zero (ƛ # 0)) (ƛ (# 0 · # 1))
   -- ƛ # 0 · (ƛ # 0)
  t6 = subst (subst-zero (ƛ # 0)) (ƛ (# 0 · # 1 · # 2))
   -- ƛ # 0 · (ƛ # 0) · # 1
  t7 = subst (subst-zero (ƛ # 0)) (ƛ ( # 2 · # 1 · # 0 · (ƛ # 2 · # 1)))
   -- ƛ # 1 · (ƛ # 0) · # 0 · (ƛ (ƛ # 0) · # 1)

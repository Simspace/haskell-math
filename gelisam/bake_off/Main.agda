module Main where

open import Data.Vec
open import Data.Vec.All
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


sym-≢ : ∀ {x y : ℕ}
      → x ≢ y
      → y ≢ x
sym-≢ x≢y y≡x = x≢y (sym y≡x)


-- type (∉) x as = ¬ (x ∈ as)
_∉_ : ∀ {n} → ℕ → Vec ℕ n → Set
x ∉ as = ¬ (x ∈ as)

head-∉ : ∀ {x a n}
       → {as : Vec ℕ n}
       → x ∉ (a ∷ as)
       → x ≢ a
head-∉ x∉as refl = x∉as here

tail-∉ : ∀ {x a n}
       → {as : Vec ℕ n}
       → x ∉ (a ∷ as)
       → x ∉ as
tail-∉ x∉a∷as x∈as = x∉a∷as (there x∈as)

nil-∉ : ∀ {x}
      → x ∉ []
nil-∉ ()

cons-∉ : ∀ {x a n}
       → {as : Vec ℕ n}
       → x ≢ a
       → x ∉ as
       → x ∉ (a ∷ as)
cons-∉ x≢a _      here         = x≢a refl
cons-∉ _   x∉a∷as (there x∈as) = x∉a∷as x∈as

∈+∉⇒≢ : ∀ {x y n}
      → {as : Vec ℕ n}
      → x ∈ as
      → y ∉ as
      → x ≢ y
∈+∉⇒≢ x∈as x∉as refl = x∉as x∈as


bump-≥ : ∀ {x min}
       → x ≥ min      -- = min ≤ x
       → x ≢ min
       → x ≥ suc min  -- = suc min ≤ x = min < x
bump-≥ min≤x x≢min = ≤+≢⇒< min≤x (sym-≢ x≢min)

bump-≥s : ∀ {min n}
        → {as : Vec ℕ n}
        → min ∉ as
        → All (λ a → a ≥     min) as
        → All (λ a → a ≥ suc min) as
bump-≥s _ []
  = []
bump-≥s {min} {suc n} {a ∷ as} min∉a∷as (a≥min ∷ as≥min)
  = a≥min+1 ∷ as≥min+1
  where
    min≢a : min ≢ a
    min≢a = head-∉ min∉a∷as

    min∉as : min ∉ as
    min∉as = tail-∉ min∉a∷as

    a≥min+1 : a ≥ suc min
    a≥min+1 = bump-≥ a≥min (sym-≢ min≢a)

    as≥min+1 : All (λ a → a ≥ suc min) as
    as≥min+1 = bump-≥s min∉as as≥min


data TwoElems (x y : ℕ) : ∀ {n} → Vec ℕ n → Set where
  here  : ∀ {n}
        → {as : Vec ℕ n}
        → y ∈ as
        → TwoElems x y (x ∷ as)
  there : ∀ {a n}
        → {as : Vec ℕ n}
        → TwoElems x y as
        → TwoElems x y (a ∷ as)

Distinct : ∀ {n} → Vec ℕ n → Set
Distinct as = ∀ {x y}
            → TwoElems x y as
            → x ≢ y

head-Distinct : ∀ {a n}
              → {as : Vec ℕ n}
              → Distinct (a ∷ as)
              → a ∉ as
head-Distinct distinct a∈as = distinct (here a∈as) refl

tail-Distinct : ∀ {a n}
              → {as : Vec ℕ n}
              → Distinct (a ∷ as)
              → Distinct as
tail-Distinct distinct twoElems = distinct (there twoElems)

nil-Distinct : Distinct []
nil-Distinct ()

cons-Distinct : ∀ {a n}
              → {as : Vec ℕ n}
              → a ∉ as
              → Distinct as
              → Distinct (a ∷ as)
cons-Distinct a∉as distinct = λ
  { (here y∈as)
    → sym-≢ (∈+∉⇒≢ y∈as a∉as)
  ; (there twoElems)
    → distinct twoElems
  }


-- remove one element from the list;
-- a 'dud' if there's one, otherwise the last element.
shorter : ∀ {n}
        → (dud : ℕ)
        → Vec ℕ (suc n)
        → Vec ℕ n
shorter _ (_ ∷ [])
  = []
shorter dud (a₁ ∷ rest@(a₂ ∷ as))
  with dud ≟ a₁
... | yes _ = rest
... | no  _ = a₁ ∷ shorter dud rest

shorter-preserves-All : ∀ {dud n}
                      → {as : Vec ℕ (suc n)}
                      → {P : ℕ → Set}
                      → All P as
                      → All P (shorter dud as)
shorter-preserves-All {as = _ ∷ []} _
  = []
shorter-preserves-All {dud = dud}
                      {as = a₁ ∷ rest@(a₂ ∷ as)}
                      (Pa₁ ∷ Prest)
  with dud ≟ a₁
... | yes _ = Prest
... | no  _ = Pa₁ ∷ shorter-preserves-All Prest

shorter-backports-∈ : ∀ {x dud n}
                    → {as : Vec ℕ (suc n)}
                    → x ∈ shorter dud as
                    → x ∈ as
shorter-backports-∈ {as = _ ∷ []} ()
shorter-backports-∈ {dud = dud}
                    {as = a₁ ∷ rest@(a₂ ∷ as)}
                    x∈shorter
  with dud ≟ a₁
... | yes _ = there x∈shorter
... | no  _ = case x∈shorter of λ
  { here
    → here
  ; (there x∈tail)
    → there (shorter-backports-∈ x∈tail)
  }

shorter-preserves-∉ : ∀ {x dud n}
                    → {as : Vec ℕ (suc n)}
                    → x ∉ as
                    → x ∉ shorter dud as
shorter-preserves-∉ x∉as x∈shorter
  = x∉as (shorter-backports-∈ x∈shorter)

shorter-preserves-Distinct : ∀ {dud n}
                           → {as : Vec ℕ (suc n)}
                           → Distinct as
                           → Distinct (shorter dud as)
shorter-preserves-Distinct {as = _ ∷ []}
                           distinct
  = nil-Distinct
shorter-preserves-Distinct {dud = dud}
                           {as = a₁ ∷ rest@(a₂ ∷ as)}
                           distinct
  with dud ≟ a₁
... | yes _ = tail-Distinct distinct
... | no  _ = cons-Distinct a₁∉shorter distinct-shorter
  where
    a₁∉rest : a₁ ∉ rest
    a₁∉rest
      = head-Distinct distinct

    a₁∉shorter : a₁ ∉ shorter dud rest
    a₁∉shorter
      = shorter-preserves-∉ a₁∉rest

    distinct-shorter : Distinct (shorter dud rest)
    distinct-shorter
      = shorter-preserves-Distinct (tail-Distinct distinct)

shorter-removes-duds : ∀ {dud n}
                     → {as : Vec ℕ (suc n)}
                     → Distinct as
                     → dud ∉ shorter dud as
shorter-removes-duds {as = _ ∷ []} _
  = nil-∉
shorter-removes-duds {dud = dud}
                     {as = a₁ ∷ rest@(a₂ ∷ as)}
                     distinct
  with dud ≟ a₁
... | yes refl  = head-Distinct distinct
... | no  dud≢a = cons-∉ dud≢a dud∉shorter
  where
    dud∉shorter : dud ∉ (shorter dud rest)
    dud∉shorter = shorter-removes-duds (tail-Distinct distinct)

shorter-bumps-min : ∀ {min n}
                  → {as : Vec ℕ (suc n)}
                  → Distinct as
                  → All (λ a → a ≥     min) as 
                  → All (λ a → a ≥ suc min) (shorter min as)
shorter-bumps-min {min = min}
                  {as = as}
                  distinct
                  as≥min
  = bump-≥s min∉shorter shorter≥min 
  where
    min∉shorter : min ∉ shorter min as
    min∉shorter = shorter-removes-duds distinct

    shorter≥min : All (λ a → a ≥ min) (shorter min as)
    shorter≥min = shorter-preserves-All as≥min


-- Let 'as' be a list of n+1 distinct integers, all 'min' or greater.
-- There ∃ an element 'as' which is 'min + n' or greater.
-- for example:
-- if n=0, then there is only one element and it is 'min' or greater.
-- if n=1, there there are two elements, one of them can be 'min' but the
-- other has to be 'min+1' or greater.
lemma : ∀ {min n}
      → {as : Vec ℕ (suc n)}
      → Distinct as
      → All (λ a → a ≥ min) as
      → ∃ λ x
      → x ∈ as
      × x ≥ n + min
lemma {as = a ∷ []} _ (a≥min ∷ [])
  = a
  , here
  , a≥min
lemma {min = min}
      {n = suc n}
      {as = as@(a₁ ∷ a₂ ∷ _)}
      distinct
      as≥min
  = case recur of λ
    { (x , x∈shorter , x≥n+min+1)
      → x
      , shorter-backports-∈ x∈shorter
      , convert x≥n+min+1
    }
  where
    distinct-shorter : Distinct (shorter min as)
    distinct-shorter
      = shorter-preserves-Distinct distinct

    shorter≥min+1 : All (λ a → a ≥ suc min) (shorter min as)
    shorter≥min+1
      = shorter-bumps-min distinct as≥min

    recur : ∃ λ x
          → x ∈ shorter min as
          × x ≥ n + suc min
    recur
      = lemma distinct-shorter shorter≥min+1
    
    convert : ∀ {x}
            → x ≥ n + suc min
            → x ≥ suc n + min
    convert {x}
      = subst (λ * → x ≥ *) (+-suc n min)

-- Let ns be a non-empty list of distinct positive integers.
-- Prove that there exists an element x of ns such that length ns ≤ x
proof : (n : ℕ)
      → (ns : Vec ℕ (suc n))
      → Distinct ns
      → All (λ a → a > 0) ns
      → ∃ λ x → x ∈ ns
              × suc n ≤ x
proof n ns distinct ns>0 = case lemma distinct ns>0 of λ
  { (x , x∈ns , x≥n+1)
  → x
  , x∈ns
  , convert x≥n+1
  }
  where
    convert : ∀ {x}
            → x ≥ n + 1
            → x ≥ suc n
    convert {x}
      = subst (λ * → x ≥ *) (+-comm n 1)

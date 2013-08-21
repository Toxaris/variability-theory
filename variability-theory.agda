module variability-theory where

open import Data.List hiding (map)
open import Relation.Binary.PropositionalEquality

-- configuration spaces

record ConfigurationSpace : Set₁ where
  field
    Config : Set
    Feature : Config → Set
    select : (config : Config) (feature : Feature config) → Config

  Variational : Set → Set
  Variational Value = Config → Value

-- Signatures

data Bind (A B : Set) : Set where
  _∷_ : A → B → Bind A B

data Empty : Set where
  [] : Empty

record Signature : Set₁ where
  field
    Sort : Set
    Symbol : List Sort → Sort → Set

  module _ (Carrier : Sort → Set) where
    Environment : List Sort → Set
    Environment [] = Empty
    Environment (sort ∷ sorts) = Bind (Carrier sort) (Environment sorts)

    Operation : List Sort → Sort → Set
    Operation sorts sort = Environment sorts → Carrier sort

  map : ∀ {A B} → (∀ {sort} → A sort → B sort) → ∀ {sorts} → Environment A sorts → Environment B sorts
  map f {[]} [] = []
  map f {sort ∷ sorts} (value ∷ env) = f value ∷ map f env

module _ (Σ : Signature) where
  open Signature Σ

  -- Algebras

  record Algebra : Set₁ where
    field
      Carrier : Sort → Set
      interp : ∀ {sorts sort} → Symbol sorts sort → Operation Carrier sorts sort

  -- Terms

  data Term (sort : Sort) : Set where
    term : ∀ {sorts} → (f : Symbol sorts sort) → Operation Term sorts sort

  terms : Algebra
  terms = record { Carrier = Term; interp = term }

  module _ (A : Algebra) where
    open Algebra A

    foldTerm : ∀ {sort} → Term sort → Carrier sort
    foldEnv : ∀ {sorts} → Environment Term sorts → Environment Carrier sorts

    foldTerm (term f env) = interp f (foldEnv env)
    foldEnv {[]} [] = []
    foldEnv {sort ∷ sorts} (t ∷ env) = foldTerm t ∷ foldEnv env

  -- Algebra homomorphisms

  record Hom (A B : Algebra) : Set where
    open Algebra
    field
      apply : ∀ {sort} → Carrier A sort → Carrier B sort
      hom : ∀ {sorts sort} (f : Symbol sorts sort) env →
        apply (interp A f env) ≡ interp B f (map apply env)

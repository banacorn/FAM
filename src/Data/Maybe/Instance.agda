module Data.Maybe.Instance where

open import Category.FAM
open import Data.Maybe
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality

instance
    MaybeFunctor : ∀ {ℓ} → Functor {ℓ} Maybe
    MaybeFunctor {ℓ} = record
        { _<$>_ = map
        ; isFunctor = record
            { identity = identity
            ; homo = homo
            }
        }
        where
            identity : ∀ {A : Set ℓ} (a : Maybe A) → map id a ≡ a
            identity (just x) = refl
            identity nothing = refl

            homo : ∀ {A B C : Set ℓ} {f : B → C} {g : A → B}
                (a : Maybe A) → map (f ∘ g) a ≡ map f (map g a)
            homo (just x) = refl
            homo nothing = refl

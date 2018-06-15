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

    MaybeApplicative : ∀ {ℓ} → Applicative {ℓ} Maybe
    MaybeApplicative {ℓ} = record
        { pure = just
        ; _⊛_ = ap
        ; isApplicative = record
            { identity = identity
            ; compose = λ {A} {B} {C} {fs} {gs} xs → compose {A} {B} {C} {fs} {gs} xs
            ; homo = λ x → refl
            ; interchange = λ {A} {B} {fs} x → interchange {A} {B} {fs} x
            }
        }
        where
            open ≡-Reasoning
            open import Function

            ap : {A B : Set ℓ} → Maybe (A → B) → Maybe A → Maybe B
            ap (just f) x = map f x
            ap nothing  x = nothing

            identity : {A : Set ℓ} (x : Maybe A) → map id x ≡ x
            identity (just x) = refl
            identity nothing = refl

            compose : {A B C : Set ℓ} {fs : Maybe (B → C)} {gs : Maybe (A → B)}
                → (xs : Maybe A)
                → ap (ap (map _∘′_ fs) gs) xs ≡ ap fs (ap gs xs)
            compose {A} {B} {C} {just fs} {just gs} (just xs) = refl
            compose {A} {B} {C} {just fs} {just gs} nothing   = refl
            compose {A} {B} {C} {just fs} {nothing} (just xs) = refl
            compose {A} {B} {C} {just fs} {nothing} nothing   = refl
            compose {A} {B} {C} {nothing} {just gs} (just xs) = refl
            compose {A} {B} {C} {nothing} {just gs} nothing   = refl
            compose {A} {B} {C} {nothing} {nothing} (just xs) = refl
            compose {A} {B} {C} {nothing} {nothing} nothing   = refl


            interchange : {A B : Set ℓ} {fs : Maybe (A → B)} (x : A) → ap fs (just x) ≡ ap (just (λ f → f x)) fs
            interchange {A} {B} {just f} x = refl
            interchange {A} {B} {nothing} x = refl

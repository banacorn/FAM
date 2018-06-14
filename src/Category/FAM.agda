module Category.FAM where

open import Level
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_; id)

------------------------------------------------------------------------
-- Functors

record IsFunctor {ℓ} (F : Set ℓ → Set ℓ)
                 (_<$>_ : ∀ {A B} → (A → B) → F A → F B)
                 : Set (suc ℓ) where
    field
        identity : {A : Set ℓ} (a : F A) → id <$> a ≡ a
        homo : ∀ {A B C} {f : B → C} {g : A → B} (a : F A)
             → (f ∘ g) <$> a ≡ f <$> (g <$> a)

record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
    infixl 4 _<$>_ _<$_
    field
        _<$>_ : ∀ {A B} → (A → B) → F A → F B
        isFunctor : IsFunctor F _<$>_

    -- An textual synonym of _<$>_
    fmap : ∀ {A B} → (A → B) → F A → F B
    fmap = _<$>_

    -- Replace all locations in the input with the same value.
    -- The default definition is fmap . const, but this may be overridden with a
    -- more efficient version.
    _<$_ : ∀ {A B} → A → F B → F A
    x <$ y = Function.const x <$> y

open Functor {{...}} public

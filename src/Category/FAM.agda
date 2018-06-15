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

    open IsFunctor isFunctor public

open Functor {{...}} public

------------------------------------------------------------------------
-- Applicatives (not indexed)

record IsApplicative {ℓ} (F : Set ℓ → Set ℓ)
                 (pure : {A : Set ℓ} → A → F A)
                 (_⊛_ : {A B : Set ℓ} → (F (A → B)) → F A → F B)
                 : Set (suc ℓ) where
    field
        identity : {A : Set ℓ} (x : F A) → pure id ⊛ x ≡ x
        compose : {A B C : Set ℓ} {f : F (B → C)} {g : F (A → B)}
            → (x : F A)
            → ((pure (λ f g → (f ∘ g)) ⊛ f) ⊛ g) ⊛ x ≡ f ⊛ (g ⊛ x)
        homo : ∀ {A B} {f : A → B} (x : A)
             → pure f ⊛ pure x ≡ pure (f x)
        interchange : ∀ {A B} {f : F (A → B)} (x : A)
            → f ⊛ pure x ≡ pure (λ f → f x) ⊛ f

record Applicative {ℓ} (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
    infixl 4 _⊛_ _<⊛_ _⊛>_
    infix  4 _⊗_

    field
        pure : {A : Set ℓ} → A → F A
        _⊛_ : {A B : Set ℓ} → (F (A → B)) → F A → F B
        isApplicative : IsApplicative F pure _⊛_

    open IsApplicative isApplicative public


    _<⊛_ : ∀ {A B} → F A → F B → F A
    x <⊛ y = x

    _⊛>_ : ∀ {A B} → F A → F B → F B
    x ⊛> y = y

    functor : Functor F
    functor = record
        { _<$>_ = λ f x → pure f ⊛ x
        ; isFunctor = record
            { identity = App.identity
            ; homo = λ {A} {B} {C} {f} {g} x →
                begin
                    pure (f ∘ g) ⊛ x
                ≡⟨ cong (λ w → _⊛_ w x) (sym (App.homo g)) ⟩
                    (pure ((λ g → (f ∘ g))) ⊛ pure g) ⊛ x
                ≡⟨ cong (λ w → (w ⊛ pure g) ⊛ x) (sym (App.homo f)) ⟩
                    ((pure (λ f g → (f ∘ g)) ⊛ pure f) ⊛ pure g) ⊛ x
                ≡⟨ App.compose x ⟩
                    pure f ⊛ (pure g ⊛ x)
                ∎
            }
        }
        where
            open ≡-Reasoning
            module App = IsApplicative isApplicative

    instance
        ApplicativeFunctor : Functor F
        ApplicativeFunctor = functor

    open import Data.Product

    _⊗_ : ∀ {A B} → F A → F B → F (A × B)
    x ⊗ y = _,_ <$> x ⊛ y

    zipWith : ∀ {A B C} → (A → B → C) → F A → F B → F C
    zipWith f x y = f <$> x ⊛ y

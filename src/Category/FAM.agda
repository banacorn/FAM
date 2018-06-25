module Category.FAM where

open import Level
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_; id; _∘′_)

------------------------------------------------------------------------
-- Functors

record IsFunctor {ℓ} (F : Set ℓ → Set ℓ)
                 (_<$>_ : ∀ {A B} → (A → B) → F A → F B)
                 : Set (suc ℓ) where
    field
        identity : {A : Set ℓ} (a : F A) → id <$> a ≡ a
        homo : ∀ {A B C} (f : B → C) (g : A → B) (a : F A)
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

-- open Functor {{...}} public

------------------------------------------------------------------------
-- Applicatives (not indexed)

record IsApplicative {ℓ} (F : Set ℓ → Set ℓ)
                 (pure : {A : Set ℓ} → A → F A)
                 (_⊛_ : {A B : Set ℓ} → (F (A → B)) → F A → F B)
                 : Set (suc ℓ) where
    field
        identity : {A : Set ℓ} (x : F A) → pure id ⊛ x ≡ x
        compose : {A B C : Set ℓ} (f : F (B → C)) (g : F (A → B))
            → (x : F A)
            → ((pure _∘′_ ⊛ f) ⊛ g) ⊛ x ≡ f ⊛ (g ⊛ x)
        homo : ∀ {A B} (f : A → B) (x : A)
             → pure f ⊛ pure x ≡ pure (f x)
        interchange : ∀ {A B} (f : F (A → B)) (x : A)
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
            ; homo = λ {A} {B} {C} f g x →
                begin
                    pure (f ∘ g) ⊛ x
                ≡⟨ cong (λ w → _⊛_ w x) (sym (App.homo (λ g → (f ∘ g)) g)) ⟩
                    (pure ((λ g → (f ∘ g))) ⊛ pure g) ⊛ x
                ≡⟨ cong (λ w → (w ⊛ pure g) ⊛ x) (sym (App.homo (λ f → _∘_ f) f)) ⟩
                    ((pure (λ f → _∘_ f) ⊛ pure f) ⊛ pure g) ⊛ x
                ≡⟨ App.compose (pure f) (pure g) x ⟩
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
    open Functor {{...}}


    _⊗_ : ∀ {A B} → F A → F B → F (A × B)
    x ⊗ y = _,_ <$> x ⊛ y

    zipWith : ∀ {A B C} → (A → B → C) → F A → F B → F C
    zipWith f x y = f <$> x ⊛ y

-- open Applicative {{...}} public
--

-- ------------------------------------------------------------------------
-- -- Monad
--
--
-- --
-- -- record IsMonad {ℓ} (M : Set ℓ → Set ℓ)
-- --                  (return : {A : Set ℓ} → A → M A)
-- --                  (_>>=_ : {A B : Set ℓ} → M A → (A → M B) → M B)
-- --                  : Set (suc ℓ) where
-- --     field
-- --         left-identity : {A B : Set ℓ} (x : A) (f : A → M B) → return x >>= f ≡ f x
-- --         right-identity : {A : Set ℓ} (xs : M A) → xs >>= return ≡ xs
-- --         assoc : {A B C : Set ℓ} (f : A → M B) (g : B → M C) → (x : M A)
-- --             → (x >>= f) >>= g ≡ (x >>= λ x' → f x' >>= g)
-- --
-- -- record Monad {ℓ} (M : Set ℓ → Set ℓ) : Set (suc ℓ) where
-- --     infixl 1 _>>=_ _>>_ _>=>_
-- --     infixr 1 _=<<_ _<=<_
-- --
-- --     field
-- --         return : {A : Set ℓ} → A → M A
-- --         _>>=_ : {A B : Set ℓ} → M A → (A → M B) → M B
-- --         isMonad : IsMonad M return _>>=_
-- --
-- --     _>>_ : ∀ {A B} → M A → M B → M B
-- --     m₁ >> m₂ = m₁ >>= λ _ → m₂
-- --
-- --     _=<<_ : ∀ {A B} → (A → M B) → M A → M B
-- --     f =<< c = c >>= f
-- --
-- --     _>=>_ : ∀ {A : Set ℓ} {B C} → (A → M B) → (B → M C) → (A → M C)
-- --     f >=> g = _=<<_ g ∘ f
-- --
-- --     _<=<_ : ∀ {A : Set ℓ} {B C} → (B → M C) → (A → M B) → (A → M C)
-- --     g <=< f = f >=> g
-- --
-- --     join : ∀ {A} → M (M A) → M A
-- --     join m = m >>= id
-- --
-- --     applicative : Applicative M
-- --     applicative = record
-- --         { pure = return
-- --         -- ; _⊛_ = λ fs xs → fs >>= λ f → xs >>= λ x → return (f x)
-- --         ; _⊛_ = λ fs xs → do
-- --             f ← fs
-- --             x ← xs
-- --             (return (f x))
-- --         ; isApplicative = record
-- --             { identity = λ xs → begin
-- --                     (return id >>= λ f → xs >>= λ x → return (f x))
-- --                 ≡⟨ Mon.left-identity id (λ f → xs >>= λ x → return (f x)) ⟩
-- --                     (xs >>= λ x → return (id x))
-- --                 ≡⟨ refl ⟩
-- --                     (xs >>= λ x → return x)
-- --                 ≡⟨ refl ⟩
-- --                     (xs >>= return)
-- --                 ≡⟨ Mon.right-identity xs ⟩
-- --                     xs
-- --                 ∎
-- --             -- { identity = λ xs → begin
-- --             --         (do
-- --             --             f ← (return id)
-- --             --             x ← xs
-- --             --             (return (f x)))
-- --             --     ≡⟨ Mon.left-identity id (λ f → do
-- --             --             x ← xs
-- --             --             (return (f x)))
-- --             --     ⟩
-- --             --         (do
-- --             --             x ← xs
-- --             --             return (id x))
-- --             --     ≡⟨ refl ⟩
-- --             --         (do
-- --             --             x ← xs
-- --             --             return x)
-- --             --     ≡⟨ Mon.right-identity xs ⟩
-- --             --         xs
-- --             --     ∎
-- --             ; compose = λ xs → begin
-- --                     {!  !}
-- --                 ≡⟨ {!   !} ⟩
-- --                     {!   !}
-- --                 ≡⟨ {!   !} ⟩
-- --                     {!   !}
-- --                 ≡⟨ {!   !} ⟩
-- --                     {!   !}
-- --                 ≡⟨ {!   !} ⟩
-- --                     {!   !}
-- --                 ∎
-- --                 -- ((pure _∘′_ ⊛ f) ⊛ g) ⊛ x ≡ f ⊛ (g ⊛ x)
-- --                 -- fs >>= λ f → xs >>= λ x → return (f x)
-- --             ; homo = {!   !}
-- --             ; interchange = {!   !} }
-- --         }
-- --         where
-- --             open ≡-Reasoning
-- --             module Mon = IsMonad isMonad
-- --
-- -- --
-- -- -- rawIApplicative : RawIApplicative M
-- -- -- rawIApplicative = record
-- -- -- { pure = return
-- -- -- ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
-- -- -- }

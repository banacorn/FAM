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


----------------------------------------------------------------------
-- Monad



record IsMonad {ℓ} (M : Set ℓ → Set ℓ)
                 (return : {A : Set ℓ} → A → M A)
                 (_>>=_ : {A B : Set ℓ} → M A → (A → M B) → M B)
                 : Set (suc ℓ) where
    field
        left-identity : {A B : Set ℓ} (x : A) (fs : A → M B) → return x >>= fs ≡ fs x
        right-identity : {A : Set ℓ} (xs : M A) → xs >>= return ≡ xs
        assoc : {A B C : Set ℓ} (x : M A) (fs : A → M B) (g : B → M C)
            → (x >>= fs) >>= g ≡ (x >>= λ x' → fs x' >>= g)
        temp : {A B : Set ℓ} (x : A) (fs : M (A → B))
            → (fs >>= λ f → return x >>= (return ∘ f)) ≡ (fs >>= λ f → (return ∘ f) x)


record Monad {ℓ} (M : Set ℓ → Set ℓ) : Set (suc ℓ) where
    infixl 1 _>>=_ _>>_ _>=>_
    infixr 1 _=<<_ _<=<_

    field
        return : {A : Set ℓ} → A → M A
        _>>=_ : {A B : Set ℓ} → M A → (A → M B) → M B
        isMonad : IsMonad M return _>>=_

    _>>_ : ∀ {A B} → M A → M B → M B
    m₁ >> m₂ = m₁ >>= λ _ → m₂

    _=<<_ : ∀ {A B} → (A → M B) → M A → M B
    f =<< c = c >>= f

    _>=>_ : ∀ {A : Set ℓ} {B C} → (A → M B) → (B → M C) → (A → M C)
    f >=> g = _=<<_ g ∘ f

    _<=<_ : ∀ {A : Set ℓ} {B C} → (B → M C) → (A → M B) → (A → M C)
    g <=< f = f >=> g

    join : ∀ {A} → M (M A) → M A
    join m = m >>= id

    congruence : ∀ {A B : Set ℓ} (fs : M A) (g h : A → M B)
        → (∀ f → g f ≡ h f)
        → (fs >>= g) ≡ (fs >>= h)
    congruence fs g h prop =
        begin
            (fs >>= g)
        ≡⟨ sym (right-identity (fs >>= g)) ⟩
            (fs >>= g >>= return)
        ≡⟨ assoc fs g return ⟩
            (fs >>= (λ f → g f >>= return))
        ≡⟨ cong (λ w → fs >>= (λ f → w f >>= return)) {!   !} ⟩
            (fs >>= (λ f → h f >>= return))
        ≡⟨ sym (assoc fs h return) ⟩
            (fs >>= h >>= return)
        ≡⟨ right-identity (fs >>= h) ⟩
            (fs >>= h)
        ∎
        where
            open ≡-Reasoning
            open IsMonad isMonad


    -- (fs >>= (λ f → return x >>= return ∘ f))
    -- (fs >>= (λ f → (return ∘ f) x))

    applicative : Applicative M
    applicative = record
        { pure = return
        ; _⊛_ = λ fs xs → fs >>= λ f → xs >>= return ∘′ f
        ; isApplicative = record
            { identity = λ xs → begin
                    (return id >>= λ f → xs >>= λ x → return (f x))
                ≡⟨ Mon.left-identity id (λ f → xs >>= λ x → return (f x)) ⟩
                    (xs >>= λ x → return (id x))
                ≡⟨ refl ⟩
                    (xs >>= λ x → return x)
                ≡⟨ refl ⟩
                    (xs >>= return)
                ≡⟨ Mon.right-identity xs ⟩
                    xs
                ∎
            -- { identity = λ xs → begin
            --         (do
            --             f ← (return id)
            --             x ← xs
            --             (return (f x)))
            --     ≡⟨ Mon.left-identity id (λ f → do
            --             x ← xs
            --             (return (f x)))
            --     ⟩
            --         (do
            --             x ← xs
            --             return (id x))
            --     ≡⟨ refl ⟩
            --         (do
            --             x ← xs
            --             return x)
            --     ≡⟨ Mon.right-identity xs ⟩
            --         xs
            --     ∎

            -- left-identity : {A B : Set ℓ} (x : A) (f : A → M B) → return x >>= f ≡ f x
            -- right-identity : {A : Set ℓ} (xs : M A) → xs >>= return ≡ xs
            -- → (x >>= f) >>= g ≡ (x >>= λ x' → f x' >>= g)
            ; compose = λ fs gs xs → begin
                    (return _∘′_ >>=
                        (λ flip → fs >>= return ∘′ flip) >>=
                        (λ f → gs >>= return ∘′ f) >>=
                        (λ f → xs >>= return ∘′ f))
                ≡⟨ cong (λ w → w >>=
                    (λ f → gs >>= return ∘′ f) >>=
                    (λ f → xs >>= return ∘′ f)) (Mon.left-identity _∘′_ (λ flip → fs >>= return ∘′ flip))
                ⟩
                    (fs >>= return ∘′ _∘′_ >>=
                        (λ f → gs >>= return ∘′ f) >>=
                        (λ f → xs >>= return ∘′ f))
                ≡⟨ Mon.assoc (fs >>= return ∘′ _∘′_) (λ f → gs >>= return ∘′ f) (λ f → xs >>= return ∘′ f) ⟩
                    ((fs >>= return ∘′ _∘′_) >>= (λ h → gs >>= return ∘′ h >>= λ f → xs >>= return ∘′ f))
                ≡⟨ {!   !} ⟩
                    -- {!   !}
                -- ≡⟨ cong (λ w → fs >>= λ r → {!   !}) {!   !} ⟩
                    (fs >>= (λ f → (gs >>= λ g → xs >>= return ∘′ g) >>= return ∘′ f))
                ∎
            ; homo = λ f x → begin
                    (return f >>= λ f' → return x >>= return ∘ f')
                ≡⟨ Mon.left-identity f (λ f' → return x >>= return ∘ f') ⟩
                    (return x >>= return ∘ f)
                ≡⟨ Mon.left-identity x (return ∘ f) ⟩
                    return (f x)
                ∎

            -- left-identity : return x >>= f ≡ f x
            -- right-identity : xs >>= return ≡ xs
            -- assoc : (x >>= f) >>= g ≡ (x >>= λ x' → f x' >>= g)
            ; interchange = λ fs x →
                begin
                    (fs >>= (λ f → return x >>= return ∘ f))
                ≡⟨ congruence fs (λ f → return x >>= return ∘ f) (λ f → (return ∘ f) x) (λ f → Mon.left-identity x (return ∘ f)) ⟩
                    (fs >>= (λ f → (return ∘ f) x))
                ≡⟨ sym (Mon.left-identity (λ f → f x) (λ f' → fs >>= (λ f → return (f' f)))) ⟩
                    (return (λ f → f x) >>= (λ f' → fs >>= (λ f → return (f' f))))
                ∎
            }
        }

    -- -- ≡⟨ sym (Mon.right-identity (fs >>= (λ f → return x >>= return ∘ f))) ⟩
    -- --     (fs >>= (λ f → return x >>= return ∘ f) >>= return)
    -- -- ≡⟨ Mon.assoc fs (λ f → return x >>= return ∘ f) return ⟩
    -- --     (fs >>= (λ f → return x >>= return ∘ f >>= return))
    -- -- ≡⟨ cong (λ w → fs >>= λ f → w f >>= return) {!   !} ⟩
    -- ≡⟨ cong (λ w → w >>= (λ f → return x >>= return ∘ f)) (sym (Mon.right-identity fs)) ⟩
    --     (fs >>= return >>= (λ f → return x >>= return ∘ f))
    -- ≡⟨ Mon.assoc fs return (λ f → return x >>= return ∘ f) ⟩
    --     (fs >>= λ f → return f >>= λ f → return x >>= return ∘ f)
    -- ≡⟨ cong (λ w → fs >>= λ f → w f) {!   !} ⟩
    --     {!   !}
    -- ≡⟨ {!   !} ⟩
    --     (fs >>= (λ f → (return ∘ f) x >>= return))
    -- ≡⟨ sym (Mon.assoc fs (λ f → return (f x)) return) ⟩
    --     ((fs >>= λ f → (return ∘ f) x) >>= return)
    -- ≡⟨ Mon.right-identity (fs >>= λ f → return (f x)) ⟩
        where
            open ≡-Reasoning
            open Applicative applicative
            module Mon = IsMonad isMonad
            --
            -- lemma :  {A B : Set ℓ} (x : A) → (λ f → return x >>= return ∘′ f) ≡ (λ f → return (f x))
            -- lemma x = begin
            --         (λ f → return x >>= return ∘′ f)
            --     ≡⟨ cong (λ w f → w) (Mon.left-identity x (λ f → {!   !})) ⟩
            --         {!   !}
            --     ≡⟨ {!   !} ⟩
            --         {!   !}
            --     ≡⟨ {!   !} ⟩
            --         {!   !}
            --     ≡⟨ {!   !} ⟩
            --         (λ f → return (f x))
            --     ∎
                -- begin
                --     (return x >>= return ∘′ f)
                -- ≡⟨ Mon.left-identity x (return ∘′ f) ⟩
                --     return (f x)
                -- ∎
            -- lemma :  {A B : Set ℓ} (x : A) (f : A → M B) → (return x >>= return ∘′ f) ≡ return (f x)
            -- lemma x f = begin
            --         (return x >>= return ∘′ f)
            --     ≡⟨ Mon.left-identity x (return ∘′ f) ⟩
            --         return (f x)
            --     ∎
--
-- rawIApplicative : RawIApplicative M
-- rawIApplicative = record
-- { pure = return
-- ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
-- }

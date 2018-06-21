module Data.List.Instance where

open import Category.FAM
open import Data.List
open import Data.List.Properties
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality hiding ([_])

instance
    ListFunctor : ∀ {ℓ} → Functor {ℓ} List
    ListFunctor = record
        { _<$>_ = map
        ; isFunctor = record
            { identity = map-id
            ; homo = map-compose
            }
        }
    ListApplicative : ∀ {ℓ} → Applicative {ℓ} List
    ListApplicative {ℓ} = record
        { pure = [_]
        ; _⊛_ = λ fs xs → concat (map (flip map xs) fs)
        ; isApplicative = record
            { identity = λ xs → begin
                    map id xs ++ []
                ≡⟨ ++-identityʳ (map id xs) ⟩
                    map id xs
                ≡⟨ map-id xs ⟩
                    xs
                ∎
            ; compose = λ {A} {B} {C} {fs} {gs} xs → compose {A} {B} {C} fs gs xs
            ; homo = λ {A} {B} {f} x → refl
            ; interchange = λ {A} {B} {fs} x → interchange fs x
            }
        }
        where
            open ≡-Reasoning
            open import Function

            concat-∷ : {A : Set ℓ} (xs : List A) (xss : List (List A))
                → concat (xs ∷ xss) ≡ xs ++ concat xss
            concat-∷ []       xss = refl
            concat-∷ (x ∷ xs) xss = refl

            concat-++ : {A : Set ℓ} (xs ys : List (List A))
                → concat (xs ++ ys) ≡ concat xs ++ concat ys
            concat-++ []         ys = refl
            concat-++ (xs ∷ xss) ys = begin
                    concat ((xs ∷ xss) ++ ys)
                ≡⟨ refl ⟩
                    concat (xs ∷ xss ++ ys)
                ≡⟨ concat-∷ xs (xss ++ ys) ⟩
                    xs ++ concat (xss ++ ys)
                ≡⟨ cong (λ x → xs ++ x) (concat-++ xss ys) ⟩
                    xs ++ concat xss ++ concat ys
                ≡⟨ sym (++-assoc xs (concat xss) (concat ys)) ⟩
                    (xs ++ concat xss) ++ concat ys
                ≡⟨ cong (λ x → x ++ concat ys) (sym (concat-∷ xs xss)) ⟩
                    concat (xs ∷ xss) ++ concat ys
                ∎

            lemma : {A B C : Set ℓ} (f : B → C) (gs : List (A → B)) (xs : List A)
                → map (flip map xs) (flip map gs (_∘′_ f)) ≡ map (map f) (map (flip map xs) gs)
            lemma f []       xs       = refl
            lemma f (g ∷ gs) xs       =
                let shit = map (flip map xs) (map (_∘′_ f) gs) in
                begin
                    flip map xs (f ∘′ g) ∷ shit
                ≡⟨ refl ⟩
                    map (f ∘′ g) xs ∷ shit
                ≡⟨ cong (λ x → x ∷ shit) (map-compose xs) ⟩
                    map f (map g xs) ∷ shit
                ≡⟨ refl ⟩
                    map f (flip map xs g) ∷ shit
                ≡⟨ cong (λ x → map f (flip map xs g) ∷ x) (lemma f gs xs) ⟩
                    map f (flip map xs g) ∷ map (map f) (map (flip map xs) gs)
                ∎

            compose : {A B C : Set ℓ} (fs : List (B → C)) (gs : List (A → B)) (xs : List A)
                → concat (map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ []))))
                    ≡ concat (map (flip map (concat (map (flip map xs) gs))) fs)
            compose []       gs xs = refl
            compose (f ∷ fs) gs xs =
                begin
                    concat (map (flip map xs) (concat (flip map gs (_∘′_ f) ∷ map (flip map gs) (map _∘′_ fs ++ []))))
                ≡⟨ cong (λ x → concat (map (flip map xs) x)) (concat-∷ (flip map gs (_∘′_ f)) (map (flip map gs) (map _∘′_ fs ++ []))) ⟩
                    concat (map (flip map xs) (flip map gs (_∘′_ f) ++ concat (map (flip map gs) (map _∘′_ fs ++ []))))
                ≡⟨ cong concat (map-++-commute (flip map xs) (flip map gs (_∘′_ f)) (concat (map (flip map gs) (map _∘′_ fs ++ [])))) ⟩
                    concat (map (flip map xs) (flip map gs (_∘′_ f)) ++ map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ []))))
                ≡⟨ concat-++ (map (flip map xs) (flip map gs (_∘′_ f))) (map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ [])))) ⟩
                    concat (map (flip map xs) (flip map gs (_∘′_ f))) ++ concat (map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ []))))
                ≡⟨ cong (λ x → concat x ++ concat (map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ []))))) (lemma f gs xs) ⟩
                    concat (map (map f) (map (flip map xs) gs)) ++ concat (map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ []))))
                ≡⟨ cong (λ x → x ++ concat (map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ []))))) (concat-map ((map (flip map xs) gs)))⟩
                    map f (concat (map (flip map xs) gs)) ++ concat (map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ []))))
                ≡⟨ refl ⟩
                    flip map (concat (map (flip map xs) gs)) f ++ concat (map (flip map xs) (concat (map (flip map gs) (map _∘′_ fs ++ []))))
                ≡⟨ cong (λ x → flip map (concat (map (flip map xs) gs)) f ++ x) (compose fs gs xs) ⟩
                    flip map (concat (map (flip map xs) gs)) f ++ concat (map (flip map (concat (map (flip map xs) gs))) fs)
                ≡⟨ sym (concat-∷ (flip map (concat (map (flip map xs) gs)) f) (map (flip map (concat (map (flip map xs) gs))) fs)) ⟩
                    concat (flip map (concat (map (flip map xs) gs)) f ∷ map (flip map (concat (map (flip map xs) gs))) fs)
                ≡⟨ refl ⟩
                    concat (map (flip map (concat (map (flip map xs) gs))) (f ∷ fs))
                ∎

            interchange : {A B : Set ℓ} (fs : List (A → B)) (x : A)
                → concat (map (flip map [ x ]) fs) ≡ concat (map (flip map fs) [ (λ g → g x) ])
            interchange [] x       = refl
            interchange (f ∷ fs) x =
                begin
                    concat (flip map [ x ] f ∷ map (flip map [ x ]) fs)
                ≡⟨ refl ⟩
                    concat (map f [ x ] ∷ map (flip map [ x ]) fs)
                ≡⟨ concat-∷ (map f [ x ]) (map (flip map [ x ]) fs) ⟩
                    map f [ x ] ++ concat (map (flip map [ x ]) fs)
                ≡⟨ cong (λ w → map f [ x ] ++ w) (interchange fs x) ⟩
                    map f [ x ] ++ map (λ z → z x) fs ++ []
                ≡⟨ refl ⟩
                    concat (flip map (f ∷ fs) (λ g → g x) ∷ [])
                ∎

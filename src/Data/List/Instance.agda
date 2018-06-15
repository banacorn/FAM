module Data.List.Instance where

open import Category.FAM
open import Data.List
open import Data.List.Properties
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
    ListApplicative = record
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
            ; compose = λ {A} {B} {C} {fs} {gs} xs → begin
                    concat (map (flip map xs)
                        (concat (map (flip map gs)
                            (map _∘′_ fs ++ []))))
                ≡⟨ cong (λ w → concat (map (flip map xs) (concat (map (flip map gs) w)))) (++-identityʳ (map (λ f g x → f (g x)) fs)) ⟩
                    concat (map (flip map xs)
                        (concat (map (flip map gs)
                            (map _∘′_ fs))))
                ≡⟨ cong (λ w → concat (map (flip map xs) (concat w))) (sym (map-compose fs)) ⟩
                    concat (map (flip map xs) (concat (map (λ f → map (λ g x → f (g x)) gs) fs)))
                ≡⟨ cong concat (sym (concat-map (map (λ f → map (λ g x → f (g x)) gs) fs))) ⟩
                    concat (concat (map (map (flip map xs)) (map (λ f → map (λ g x → f (g x)) gs) fs)))
                ≡⟨ cong (concat ∘ concat) (sym (map-compose fs)) ⟩
                    concat (concat (map ((map (flip map xs)) ∘ (λ f → map (λ g x → f (g x)) gs)) fs))
                ≡⟨ {!   !} ⟩
                    {!   !}
                ≡⟨ {!   !} ⟩
                    (concat ∘ map ((flip map ∘ concat ∘ map (flip map xs)) gs)) fs
                ≡⟨ refl ⟩
                    concat (map (flip map (concat (map (flip map xs) gs))) fs)
                ∎

-- concat
--      (map (λ f → map f xs)
--       (concat
--        (map (λ f → map f .g)
        -- (concat (map (λ f → _∘_ (λ {.x} → f)) .f ∷ [])))))
--      ≡
                -- concat (map (λ f → map f (concat (map (λ f₁ → map f₁ xs) .g))   ) .f)
            ; homo = {!   !}
            ; interchange = {!   !}
            }
        }
        where
            open ≡-Reasoning
            open import Function

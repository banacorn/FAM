module Data.List.Instance where

open import Category.FAM
open import Data.List
open import Data.List.Properties

instance
    ListFunctor : ∀ {ℓ} → Functor {ℓ} List
    ListFunctor = record
        { _<$>_ = map
        ; isFunctor = record
            { identity = map-id _
            ; homo = map-compose _
            }
        }

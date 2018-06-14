module Test where

open import Data.List
open import Data.List.Instance
open import Data.Nat
open import Category.FAM

f : List ℕ → List ℕ
f = fmap suc

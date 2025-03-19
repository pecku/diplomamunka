{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Lib
open import model

module SimpleKripke
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  where

SK : Model funar relar
SK = {!   !}
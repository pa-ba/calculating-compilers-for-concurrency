{-# OPTIONS --copatterns --sized-types --guardedness #-}

module CTree where

open import Size public

open import CTree.Definitions public
open import CTree.IndexedBisimilarity public
open import CTree.Bisimilarity public


data None : Set → Set where

instance
  nonePar : Concurrent None
  _⇄_ {{nonePar}} ()

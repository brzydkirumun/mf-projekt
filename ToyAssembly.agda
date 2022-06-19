module ToyAssembly where

open import Data.Nat
open import Data.List
open import Data.Bool

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

{- Pomocniczne struktury -}

-- Czy dwie liczby naturalne są równe?
_≡ℕ?_ : ℕ → ℕ → Bool
zero ≡ℕ? zero   = true
zero ≡ℕ? suc m  = false
suc n ≡ℕ? zero  = false
suc n ≡ℕ? suc m = n ≡ℕ? m

-- Para uporządkowana liczb naturalnych
data Pair : Set where
  ⟨_,_⟩ : ℕ → ℕ → Pair

-- Maybe
data Maybe : Set where
  Nothing : Maybe
  Just_   : ℕ → Maybe

-- Przegrzebuje listę par z ℕ² i zwraca 2. koordynat pierwszej napotkanej
-- pary z n-em na pierwszej współrzędnej
valOf : List Pair → ℕ → Maybe
valOf [] n                = Nothing
valOf (⟨ x , x₁ ⟩ ∷ ns) n = if x ≡ℕ? n then (Just x₁) else valOf ns n

-- Dodaje parę do listy. Jeżeli w liście istnieje już para z taką samą pierwszą
-- współrzędną, to zamiast dodawać kolejną, zmienia drugą współrzędną na tę
-- dodawanej.
push : List Pair → Pair → List Pair
push [] n = n ∷ []
push (⟨ x , x₁ ⟩ ∷ ns) ⟨ x₂ , x₃ ⟩
  = if x ≡ℕ? x₂ then (⟨ x , x₃ ⟩ ∷ ns) else (⟨ x , x₁ ⟩ ∷ push ns ⟨ x₂ , x₃ ⟩)

-- Testy pusha
push-test-1 : push [] ⟨ 0 , 1 ⟩ ≡ ⟨ 0 , 1 ⟩ ∷ []
push-test-1 = refl

push-test-2 : push (⟨ 0 , 1 ⟩ ∷ []) ⟨ 1 , 2 ⟩ ≡ ⟨ 0 , 1 ⟩ ∷ ⟨ 1 , 2 ⟩ ∷ []
push-test-2 = refl

push-test-3 : push (⟨ 0 , 1 ⟩ ∷ ⟨ 1 , 2 ⟩ ∷ []) ⟨ 0 , 5 ⟩ ≡ ⟨ 0 , 5 ⟩ ∷ ⟨ 1 , 2 ⟩ ∷ []
push-test-3 = refl


{- Arytmetyka -}

-- Typ
data L1 : Set where
  n_  : ℕ → L1
  _̂+_ : L1 → L1 → L1
  _̂*_ : L1 → L1 → L1

-- Semantyka
s1 : L1 → ℕ
s1 (n x)    = x
s1 (l ̂+ l₁) = s1 l + s1 l₁
s1 (l ̂* l₁) = s1 l * s1 l₁


{- Język asemblera -}

-- Model automatu
record M : Set where
  field
    mem : List Pair
    acc : Maybe
    err : Bool

-- Operatory
data A : Set where
  end   : A
  set   : ℕ → A → A
  add   : ℕ → A → A
  mul   : ℕ → A → A
  load  : ℕ → A → A
  store : ℕ → A → A

-- Programy
data L2 : Set where
  Begin_ : A → L2

-- Kroki przy rozważaniu semantyki
step : M → L2 → M
step state (Begin end)
  = state

step record { mem = mem ; acc = acc ; err = err } (Begin set x x₁)
  = step record { mem = mem; acc = Just x; err = err } (Begin x₁)

step record { mem = mem ; acc = Nothing ; err = err } (Begin add x x₁)
  = record { mem = []; acc = Nothing; err = true }
step record { mem = mem ; acc = (Just x₂) ; err = err } (Begin add x x₁)
  = step record { mem = mem; acc = (Just (x + x₂)); err = err } (Begin x₁)

step record { mem = mem ; acc = Nothing ; err = err } (Begin mul x x₁)
  = record { mem = []; acc = Nothing; err = true }
step record { mem = mem ; acc = (Just x₂) ; err = err } (Begin mul x x₁)
  = step record { mem = mem; acc = (Just (x * x₂)); err = err } (Begin x₁)

step record { mem = mem ; acc = acc ; err = err } (Begin load x x₁)
  = step record { mem = mem; acc = (valOf mem x); err = err } (Begin x₁)

step record { mem = mem ; acc = Nothing ; err = err } (Begin store x x₁)
  = record { mem = []; acc = Nothing; err = true }
step record { mem = mem ; acc = (Just x₂) ; err = err } (Begin store x x₁)
  = step record { mem = push mem ⟨ x , x₂ ⟩; acc = (Just x₂) ; err = err } (Begin x₁)

-- Semantyka
s2 : L2 → M
s2 = step record { mem = []; acc = Nothing; err = false }

-- Dowody, że to działa dla przykładowych programów
prog-test-end : s2 (Begin end) ≡ record { mem = []; acc = Nothing; err = false }
prog-test-end = refl

prog-test-set : ∀ (x : ℕ) → s2 (Begin (set x end)) ≡ record { mem = []; acc = Just x; err = false }
prog-test-set = λ x → refl

prog-test-add : ∀ (x₁ x₂ : ℕ) → s2 (Begin (set x₁ (add x₂ end))) ≡ record { mem = []; acc = Just (x₂ + x₁); err = false }
prog-test-add = λ x₁ x₂ → refl

prog-test-mul : ∀ (x₁ x₂ : ℕ) → s2 (Begin (set x₁ (mul x₂ end))) ≡ record { mem = []; acc = Just (x₂ * x₁); err = false }
prog-test-mul = λ x₁ x₂ → refl

prog-test-store : ∀ (x m : ℕ) → s2 (Begin (set x (store m end))) ≡ record { mem = ⟨ m , x ⟩ ∷ []; acc = Just x; err = false }
prog-test-store = λ x m → refl

prog-1       = Begin (set 1 (store 0 (set 2 (store 1 (load 0 end)))))
prog-1-exp   = record { mem = ⟨ 0 , 1 ⟩ ∷ ⟨ 1 , 2 ⟩ ∷ []; acc = Just 1; err = false }
prog-1-proof : s2 prog-1 ≡ prog-1-exp
prog-1-proof = refl

{- Kompilator -}

c : L1 → L2
c (n x)      = {!!}
c (cs ̂+ cs₁) = {!!}
c (cs ̂* cs₁) = {!!}

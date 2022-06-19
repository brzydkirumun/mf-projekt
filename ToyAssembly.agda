module ToyAssembly where

open import Data.Nat
open import Data.List
open import Data.Bool

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
  = if x ≡ℕ? x₂ then (⟨ x , x₃ ⟩ ∷ ns) else ⟨ x , x₁ ⟩ ∷ push ns ⟨ x₂ , x₃ ⟩


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

-- Semantyka
s2 : L2 → M
s2 = step record { mem = []; acc = Nothing; err = false }
  where
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
      = record { mem = push mem ⟨ x , x₂ ⟩; acc = (Just x₂) ; err = err }


{- Kompilator -}

c : L1 → L2
c (n x)      = {!!}
c (cs ̂+ cs₁) = {!!}
c (cs ̂* cs₁) = {!!}

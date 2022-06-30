module ToyAssembly where

open import Data.List
open import Data.Bool
open import Data.Nat
open import Maybe

-- Para uporządkowana
data Pair (A B : Set) : Set where
  ⟨_,_⟩ : A -> B -> Pair A B

fst : {A B : Set} -> Pair A B -> A
fst ⟨ a , _ ⟩ = a

-- Czy dwie liczby naturalne są równe?
_≡ℕ?_ : ℕ -> ℕ -> Bool
zero ≡ℕ? zero   = true
zero ≡ℕ? suc m  = false
suc n ≡ℕ? zero  = false
suc n ≡ℕ? suc m = n ≡ℕ? m

-- Wyciąganie danych z tablicy asocjacyjnej z cakowitymi kluczami
vlookup : {A : Set} -> ℕ -> List (Pair ℕ A) -> Maybe A
vlookup x []               = Nothing
vlookup x (⟨ k , v ⟩ ∷ ps) = if x ≡ℕ? k then Just v else vlookup x ps

-- Wtykanie danych do tablicy asocjacyjnej z całkowitymi kluczami
insert : {A : Set} -> Pair ℕ A -> List (Pair ℕ A) -> List (Pair ℕ A)
insert x []       = x ∷ []
insert x (p ∷ ps) = if fst x ≡ℕ? fst p then x ∷ ps else p ∷ insert x ps

-- Arytmetyka
data L1 : Set where
  ̇n_  : ℕ -> L1
  _̇+_ : L1 -> L1 -> L1
  _̇*_ : L1 -> L1 -> L1

-- Semantyka języka L1
s1 : L1 → ℕ
s1 (̇n x)    = x
s1 (x ̇+ x₁) = s1 x + s1 x₁
s1 (x ̇* x₁) = s1 x * s1 x₁

-- Model automatu
record M : Set where
  field
    mem : List (Pair ℕ ℕ)
    acc : Maybe ℕ

-- Operatory
data A : Set where
  end   : A
  set   : ℕ -> A -> A
  add   : ℕ -> A -> A
  mul   : ℕ -> A -> A
  load  : ℕ -> A -> A
  store : ℕ -> A -> A

-- Programy
data L2 : Set where
  Begin_ : A -> L2

-- Punkt wyjściowy automatu
start : M
start = record { mem = [] ; acc = Nothing }

-- Backend funkcji semantyki dla L2
step : Pair M L2 → Maybe M
step ⟨ state , Begin end ⟩
  = Just state

step ⟨ state , Begin set x x₁ ⟩
  = Just ⟨ record { mem = M.mem state ; acc = Just x } , Begin x₁ ⟩ >>= step

step ⟨ state , Begin add x x₁ ⟩ with appMaybe (M.acc state) (vlookup x (M.mem state)) _+_
... | Nothing = Nothing
... | Just n  = Just ⟨ record { mem = M.mem state ; acc = Just n } , Begin x₁ ⟩ >>= step

step ⟨ state , Begin mul x x₁ ⟩ with appMaybe (M.acc state) (vlookup x (M.mem state)) _*_
... | Nothing = Nothing
... | Just n  = Just ⟨ record { mem = M.mem state ; acc = Just n } , Begin x₁ ⟩ >>= step

step ⟨ state , Begin load x x₁ ⟩ with vlookup x (M.mem state)
... | Nothing = Nothing
... | Just n  = Just ⟨ record { mem = M.mem state ; acc = Just n } , Begin x₁ ⟩ >>= step

step ⟨ state , Begin store x x₁ ⟩ with M.acc state
... | Nothing = Nothing
... | Just n  = Just ⟨ record { mem = insert ⟨ x , n ⟩ (M.mem state) ; acc = M.acc state } , Begin x₁ ⟩ >>= step

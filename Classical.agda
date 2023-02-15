module Classical where

open import Logic

K : {P Q : Set} → P → Q → P
K p q = p

S : {P Q R : Set} → (P → Q → R) → (P → Q) → (P → R)
S = λ pqr → λ pq → λ p → pqr p (pq p)

-- K and S are universal for the fragment of propositional logic that contains only implication.

orcase : {P Q R : Set} → (P → R) → (Q → R) → (P ∨ Q → R)
orcase pr qr (inl p) = pr p
orcase pr qr (inr q) = qr q

excluded-middle : Set₁
excluded-middle = {P : Set} → P ∨ ¬ P

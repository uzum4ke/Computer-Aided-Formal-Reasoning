module Classical where

-- In this module we contrast classical logic (Where Prop ≡ Bool) with our
-- constructive logic (Prop ≡ Set).

open import Logic

K : {P Q : Set} → P → Q → P
K p q = p

S : {P Q R : Set} → (P → Q → R) → (P → Q) → (P → R)
S = λ pqr → λ pq → λ p → pqr p (pq p)

-- K and S are universal for the fragment of propositional logic that contains only implication.

orcase : {P Q R : Set} → (P → R) → (Q → R) → (P ∨ Q → R)
orcase pr qr (inl p) = pr p
orcase pr qr (inr q) = qr q

-- The following type, known as the law of excluded middle, is not constructible for all P in
-- our system.
 
excluded-middle : Set₁
excluded-middle = {P : Set} → ¬ P ∨ P

-- This definition says that given an arbitrary P either we can construct P or we can construct
-- ¬ P.
-- But the process to construct P ∨ ¬ P may contain an infinite loop, never constructing either
-- P ∨ ¬ P.

-- Next we define reductio ad absurdum.

¬¬ : Set → Set
¬¬ P = ¬ (¬ P)

RAA : Set₁
RAA = {P : Set} → ¬¬ P → P

-- This is a type of proof that occurs frequently when doing mathematics in classical logic, where
-- it is a true proposition, unfortunately in constructive logic, it is not provable.

-- The other direction of implication is fine though:
--   If P is constructible then it then the construction 'P implies a witness for ⊥'
--   is unconstructible.

raainv : {P : Set} → P → ¬¬ P 
raainv p np = np p

-- Another construction one comes across in classical logic is the equivalence between
-- implication and negation and disjunction: (P → Q) ⇔ ( ¬ P ∨ Q). This also does not hold
-- in constructive logic.

-- The following part of the biimplication does hold though
→-¬-∨ : {P Q : Set} → (¬ P ∨ Q) → (P → Q)
→-¬-∨ (inl np) p = efq (np p)
→-¬-∨ (inr q) p = q

-- Although excluded middle isn't constructible in our system, its double negation is!

¬¬-excluded-middle : {P : Set} → ¬¬ (¬ P ∨ P)
¬¬-excluded-middle nporp = nporp (inl (λ x → nporp (inr x))) 

-- This essentially says that excluded middle doesn't break our system: for some constructions exc-- luded middle is possible, or if excluded middle is never possible then we have a witness to ⊥.

-- As a consequence of we have ¬¬ (¬ P ∨ P) ⇔ (¬ P ∨ P)
RAA→LEM : RAA → excluded-middle
RAA→LEM raa = raa ¬¬-excluded-middle



LEM→RAA : {P : Set} → (¬ P ∨ P) → (¬¬ P → P)
LEM→RAA (inl np) nnp = efq (nnp np)
LEM→RAA (inr p) nnp = p


--  and also the double negation of the last deMorgan law:
¬¬deMorgan¬∧ : {P Q : Set} → ¬ (P ∧ Q) → ¬¬ ((¬ P) ∨ (¬ Q))
¬¬deMorgan¬∧ npandq npornq = npornq (inl (λ x → npornq (inr (λ x₁ → npandq (x , x₁)))))

module Logic where


-- In constructive logic we identify the type of sets and the type of propositions


data ⊥ : Set where

-- We can view ⊥ as a special case of ∨ with no arguments.

-- ⊥ is powerful, if we had a construction of ⊥ then we would have a construction of anything at all, note a language of contruction without this rule (also known as the rule of explosion) is called minimal logic.

efq : {P : Set} → ⊥ → P
efq ()

-- If a construction P can be used to give a witness to ⊥ then that construction cannot be, we denote this by ¬

¬ : Set → Set
¬ P = P → ⊥

-- Simplest type with a constructive meaning, that is, the simplest object in our
-- theory that is nonempty

data ⊤ : Set where
    tt : ⊤

-- Propositions imply themselves
-- Equivalently this is a definition of the polymorphic identity function
ID : (P : Set) → P → P
ID = λ P p → p

I : {P : Set} → P → P
I {P} p = ID P p

-- Definition of Conjunction
data _∧_ (P Q : Set) : Set where
  _,_ : P → Q → P ∧ Q 

infixr 2 _∧_

-- ∧ is commutative 
∧-comm : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm (p , q) = q , p

-- Definition of Disjunction
data _∨_ (P Q : Set) : Set where
 inl : P → P ∨ Q
 inr : Q → P ∨ Q

infixr 1 _∨_

-- ∨ is commutative
∨-comm : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
∨-comm (inl x) = inr x
∨-comm (inr x) = inl x


_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) ∧ (Q → P)

infixr 0 _⇔_

-- ∧ distributes over ∨
distrib-∧-∨ : {P Q R : Set} →  P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
distrib-∧-∨ =  dist-∧-∨ , dist-∧-∨-op
  where
    dist-∧-∨ : {P Q R : Set} → P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)
    dist-∧-∨ (p , inl q) = inl (p , q)
    dist-∧-∨ (p , inr r) = inr (p , r)

    dist-∧-∨-op : {P Q R : Set} → (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)
    dist-∧-∨-op (inl (p , q)) = p , inl q
    dist-∧-∨-op (inr (p , r)) = p , inr r

-- It cannot be that there is a construction P and that construction P gives a witness to ⊥
contradiction : {P : Set} → ¬ (P ∧ ¬ P)
contradiction (p , np) = np p

contrapos : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
contrapos piq nq p = nq (piq p)

deMorgan¬∨ : {P Q : Set} → ¬ (P ∨ Q) → ¬ P ∧ ¬ Q 
deMorgan¬∨ nporq = (λ p → nporq (inl p)) , (λ q → nporq (inr q))
  
deMorgan¬∧¬ : {P Q : Set} → (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q)
deMorgan¬∧¬ (np , nq) (inl npor) = np npor
deMorgan¬∧¬ (np , nq) (inr nqor) = nq nqor
  
deMorgan¬∨¬ : {P Q : Set} → (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q)
deMorgan¬∨¬ (inl np) (p , q) = np p
deMorgan¬∨¬ (inr np) (p , q) = np q

--  The last one turns out not to be provable!

--deMorgan¬∧ : {P Q : Set} → ¬ (P ∧ Q) → (¬ P) ∨ (¬ Q)
--deMorgan¬∧ npq = inr (λ q → npq ({!!} , q))

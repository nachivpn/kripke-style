--
-- Definition of Hilbert-style logical systems in Agda
--

module Systems where

infixr 10 _⇒_
infixr 11 _∧_ _∨_

-- Proposotional formulas
data Form : Set where

  -- atoms (or propositional variables)
  p q p' q' : Form

  -- falsity/absurdity
  ⊥              : Form
  
  -- binary connectives
  _∧_ _∨_ _⇒_    : Form → Form → Form
  
  -- modal connective
  ◻_             : Form → Form

-- negation
¬_ : Form → Form
¬ A = A ⇒ ⊥

-- possibility
◇ : Form → Form
◇ A = ¬ ◻ ¬ A

variable
  A B C : Form

-- Logical systems
record Sys : Set₁ where
  field

    -- Derivations (of a formula)
    𝒟 : Form → Set
   
    -- Implication axioms (named after Schönfinkel/Curry's S and K combinators)
    ImpK : 𝒟 (A ⇒ B ⇒ A)
    ImpS : 𝒟 ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C))
    
    -- Disjunction axioms
    OrI1  : 𝒟 (A ⇒ A ∨ B)
    OrI2  : 𝒟 (B ⇒ A ∨ B)
    OrE   : 𝒟 ((A ⇒ C) ⇒ (B ⇒ C) ⇒ (A ∨ B ⇒ C))
    
    -- Conjunction axioms
    AndE1 : 𝒟 (A ∧ B ⇒ A)
    AndE2 : 𝒟 (A ∧ B ⇒ B)
    AndI  : 𝒟 (A ⇒ B ⇒ A ∧ B)
    
    -- Absurdity axiom
    AbsE  : 𝒟 (⊥ ⇒ A)

    -- Modus Ponens rule
    MP    : 𝒟 (A ⇒ B) → 𝒟 A → 𝒟 B

  -- (named after combinator I)
  ImpI : 𝒟 (C ⇒ C)
  ImpI {C} = MP (MP ImpS ImpK) (ImpK {A = C} {B = C})

-- Systems for classical propositional logic
record SysCPL (SL : Sys) : Set₁ where
  
  open Sys SL

  field
    LEM : 𝒟 (A ∨ ¬ A)

-- Systems for classical modal logic (also known as normal modal logic)
record SysCML (SL : Sys) : Set₁ where

  open Sys SL

  field

    CML  : SysCPL SL
    
    -- Modal axiom K (not be confused with combinator K above)
    BoxK  : 𝒟 (◻ (A ⇒ B) ⇒ ◻ A ⇒ ◻ B)
    
    -- Necessitation rule
    Nec  : 𝒟 A → 𝒟 (◻ A)

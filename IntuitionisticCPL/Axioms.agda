-- Constructive Provability Logic 
-- Tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Valid and invalid axioms

module IntuitionisticCPL.Axioms where
open import Prelude hiding (⊥ ; ¬)
open import Accessibility.Inductive
open import Accessibility.Five
open import Accessibility.IndexedList
open import IntuitionisticCPL.Core
open import IntuitionisticCPL.Sequent
open import IntuitionisticCPL.Equiv

¬ : Type → Type
¬ A = A ⊃ ⊥

module PROPERTIES (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 

   Trans : Set
   Trans = ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃

   Con : MCtx → W → Set
   Con Γ w = ∀ {w'} → w ≺ w' → Γ ⊢ ⊥ [ w' ] → Void

module AXIOMS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open PROPERTIES UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF
   open EQUIV UWF

   -- Axioms of intuitionstic propositional logic (Theorem 3.1)
   axI : ∀{Γ A w} 
      → Γ ⊢ A ⊃ A [ w ]
   axI = ⊃I (hyp Z)

   axK : ∀{Γ A B w}
      → Γ ⊢ A ⊃ B ⊃ A [ w ]
   axK = ⊃I (⊃I (hyp (S Z)))

   axS : ∀{Γ A B C w}
      → Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C [ w ]
   axS = ⊃I (⊃I (⊃I (⊃E (⊃E (hyp (S (S Z))) (hyp Z)) (⊃E (hyp (S Z)) (hyp Z)))))
   
   ax⊥E : ∀{Γ A w}
      → Γ ⊢ ⊥ ⊃ A [ w ]
   ax⊥E = ⊃I (⊥E (hyp Z))

   -- Necessitation rule (Theorem 3.2)
   Nec : ∀{Γ A} 
      → (∀{w} → Γ ⊢ A [ w ])
      → (∀{w} → Γ ⊢ □ A [ w ])
   Nec D = □I (λ ω → D) 

   -- Axioms of IK, Simpson's intuitionistic modal logic (Theorem 3.3)
   axK□ : ∀{Γ A B w}
      → Γ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B [ w ]
   axK□ = ⊃I (⊃I (□E (hyp (S Z))
      λ DAB → □E (hyp Z) 
      λ DA → □I (λ ω → ⊃E (DAB ω) (DA ω))))

   axK◇ : ∀{Γ A B w}
      → Γ ⊢ □ (A ⊃ B) ⊃ ◇ A ⊃ ◇ B [ w ]
   axK◇ = ⊃I (⊃I (□E (hyp (S Z)) 
      λ DAB → ◇E (hyp Z) 
      λ ω DA → ◇I ω (⊃E (DAB ω) DA)))

   ax4□ : ∀{Γ A w}
      → Trans
      → Γ ⊢ □ A ⊃ □ (□ A) [ w ]
   ax4□ _≺≺_ = ⊃I (□E (hyp Z) 
      λ D → □I λ ω → □I λ ω' → D (ω ≺≺ ω'))

   -- Provability logic (Theorem 3.4)
   axGL : ∀{Γ A w}
      → Trans
      → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   axGL {A = A} _≺≺_ = ind P lemma _
    where
      P : W → Set
      P = λ w → ∀{Γ} → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   
      lemma : (w : W) → ((w' : W) → w ≺ w' → P w') → P w
      lemma w ih = ⊃I (□E (hyp Z) 
         λ DInd → □I 
         λ ω → ⊃E (DInd ω) (⊃E (ih _ ω) (□I (λ ω' → DInd (ω ≺≺ ω')))))

   -- Löb rule (Theorem 3.5)
   Löb : ∀{Γ A}
      → (∀{w} → Γ ⊢ □ A ⊃ A [ w ])
      → (∀{w} → Γ ⊢ A [ w ])
   Löb {A = A} D = {!!}

   -- De Morgan dualities (Theorem 3.6)
   ax◇¬ : ∀{Γ A w} 
      → Con Γ w 
      → Γ ⊢ ◇ (¬ A) ⊃ ¬ (□ A) [ w ]
   ax◇¬ con = ⊃I {!!}

   ax□¬ : ∀{Γ A w} 
      → Con Γ w 
      → Γ ⊢ □ (¬ A) ⊃ ¬ (◇ A) [ w ]
   ax□¬ con = ⊃I {!!}
   
module NON-AXIOMS where
   open TRANS-UWF Example
   open PROPERTIES Example
   open ILIST Example
   open CORE Example
   open SEQUENT Example
   open EQUIV Example

   Q : Type
   Q = a "Q"   

   -- Axioms of IK, Simpson's intuitionistic modal logic (Theorem 3.3)
   ax◇⊥ : [ ⊥ at δ ] ⇒ ¬ (◇ ⊥) [ β ] → Void
   ax◇⊥ D = {!!}

   ax4□ : [] ⇒ ◇ (◇ Q) ⊃ ◇ Q [ α ] → Void
   ax4□ (⊃L () _ _)
   ax4□ (⊥L ()) 
   ax4□ (◇L () _)
   ax4□ (□L () _)
   ax4□ (¬◇L () _) 
   ax4□ (¬□L () _) 
   ax4□ (⊃R D) = {!!}
    where
      lem3 : ∀{w} → [] ⇒ Q [ w ] → Void
      lem3 (hyp ())
      lem3 (⊃L () _ _)
      lem3 (⊥L ()) 
      lem3 (◇L () _)
      lem3 (□L () _)
      lem3 (¬◇L () _) 
      lem3 (¬□L () _) 

{-
      lem2 : ∀{w} → α ≺ w → (◇ (◇ Q) at α :: ⇒ Q [ w ] → [] ⇒ Q [ w ]
      lem2 = {!!}
  -}    
      lem1 : [ ◇ (◇ Q) at α ] ⇒ ◇ Q [ α ] → Void
      lem1 (⊃L (S ()) _ _)
      lem1 (⊥L (S ())) 
      lem1 (◇R ω D) = lem3 {!!} -- (lem2 ω D)
      lem1 (◇L Z D) = {!!}
      lem1 (◇L (S ()) _)
      lem1 (□L (S ()) _)
      lem1 (¬◇L (S ()) _) 
      lem1 (¬□L (S ()) _) 

   axIK : [] ⇒ (◇ Q ⊃ □ ⊥) ⊃ □ (Q ⊃ ⊥) [ β ] → Void
   axIK D = {!!} 

   -- De Morgan dualities (Theorem 3.6)
   ax¬□ : [] ⇒ ¬ (□ Q) ⊃ ◇ (¬ Q) [ α ] → Void
   ax¬□ D = {!!}

   ax□¬ : [ Q at α ] ⇒ ¬ (◇ Q) ⊃ □ (¬ Q) [ α ] → Void
   ax□¬ D = {!!}


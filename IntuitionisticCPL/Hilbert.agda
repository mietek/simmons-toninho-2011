-- Constructive Provability Logic 
-- The intuitionistic, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Valid axioms

module IntuitionisticCPL.Hilbert where
open import Prelude hiding (⊥ ; ¬)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import IntuitionisticCPL.Core
open import IntuitionisticCPL.Sequent
open import IntuitionisticCPL.Equiv

¬ : Type → Type
¬ A = A ⊃ ⊥

data Axiom : Type → Set where
   I : ∀{A} → Axiom (A ⊃ A)
   K : ∀{A B} → Axiom (A ⊃ B ⊃ A)
   S : ∀{A B C} → Axiom ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
   ⊥E : ∀{A} → Axiom (⊥ ⊃ A)
   □K : ∀{A B} → Axiom (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
   ◇K : ∀{A B} → Axiom (□ (A ⊃ B) ⊃ ◇ A ⊃ ◇ B)
   ¬□K : ∀{A B} → Axiom (□ (A ⊃ B) ⊃ ¬□ B ⊃ ¬□ A)
   ¬◇K : ∀{A B} → Axiom (□ (A ⊃ B) ⊃ ¬◇ B ⊃ ¬◇ A)
   □N : ∀{A B} → Axiom (¬□ A ⊃ □ A ⊃ B)
   ◇N : ∀{A B} → Axiom (¬◇ A ⊃ ◇ A ⊃ B)
   □C : ∀{A} → Axiom (□ A ⊃ ¬◇ (A ⊃ ⊥))
   ◇C : ∀{A} → Axiom (◇ A ⊃ ¬□ (A ⊃ ⊥))

data TransAxiom : Type → Set where
   □4 : ∀{A} → TransAxiom (□ A ⊃ □ (□ A))
   GL : ∀{A} → TransAxiom (□ (□ A ⊃ A) ⊃ □ A)

module PROPERTIES (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 

   Trans : Set
   Trans = ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃

   Con : MCtx → W → Set
   Con Γ w = ∀ {w'} → w ≺ w' → Γ ⇒ ⊥ [ w' ] → Void

   Empty : MCtx → W → Set
   Empty Γ w = ∀ {A} → A at w ∈ Γ → Void

   DecideA : MCtx → Type → W → Set
   DecideA Γ A w = Sum 
      (∀ {w'} → w ≺ w' → Γ ⇒ A [ w' ])
      (∃ λ w' → (w ≺ w') × (Γ ⇒ A [ w' ] → Void))

   Decide¬A : MCtx → Type → W → Set
   Decide¬A Γ A w = Sum 
      (∀ {w'} → w ≺ w' → Γ ⇒ A [ w' ] → Void)
      (∃ λ w' → (w ≺ w') × (Γ ⇒ A [ w' ]))

   DecideA-InCPL : MCtx → Type → W → Set
   DecideA-InCPL Γ A w = Sum 
      (∀ {w'} → w ≺ w' → Γ ⇒ A [ w' ])
      (∃ λ w' → (w ≺ w') × (Γ ⇒ ¬ A [ w' ]))

   Decide¬A-InCPL : MCtx → Type → W → Set
   Decide¬A-InCPL Γ A w = Sum 
      (∀ {w'} → w ≺ w' → Γ ⇒ ¬ A [ w' ])
      (∃ λ w' → (w ≺ w') × (Γ ⇒ A [ w' ]))


   Decide◇A-InCPL : MCtx → Type → W → Set
   Decide◇A-InCPL Γ A w = Sum 
      (∀ {w'} → w ≺ w' → (Γ ⇒ ¬ A [ w' ] → Void) → (¬□ (A ⊃ ⊥)) at w :: Γ ⇒ ◇ A [ w ])           
      (∃ λ w' → (w ≺ w') × (Γ ⇒ A [ w' ]))




module SOUNDNESS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open PROPERTIES UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF
   open EQUIV UWF

   -- Valid Axioms
   validaxioms : ∀{Γ A w} 
      → Axiom A 
      → (∀ {w' Γ} → w ≺ w' → Γ ⊢ ⊥ [ w' ] → Void) 
      → Γ ⊢ A [ w ]

   -- Regular old logic
   validaxioms I con = ⊃I (hyp Z)
   validaxioms K con = ⊃I (⊃I (hyp (S Z)))
   validaxioms S con =
      ⊃I (⊃I (⊃I (⊃E (⊃E (hyp (S (S Z))) (hyp Z)) (⊃E (hyp (S Z)) (hyp Z)))))
   validaxioms ⊥E con = ⊃I (⊥E (hyp Z))  

   -- Modal logic
   validaxioms □K con = ⊃I (⊃I (□E (hyp (S Z))
      λ DAB → □E (hyp Z) 
      λ DA → □I (λ ω → ⊃E (DAB ω) (DA ω))))
   validaxioms ◇K con = ⊃I (⊃I (□E (hyp (S Z)) 
      λ DAB → ◇E (hyp Z) 
      λ ω DA → ◇I ω (⊃E (DAB ω) DA)))
   validaxioms ¬□K con = ⊃I (⊃I (□E (hyp (S Z)) 
      λ DAB → ¬□E (hyp Z) 
      λ ω DB → ¬□I ω (λ DA → DB (⊃E (DAB ω) DA))))
   validaxioms ¬◇K con = ⊃I (⊃I (□E (hyp (S Z)) 
      λ DAB → ¬◇E (hyp Z) 
      λ DB → ¬◇I (λ ω DA → DB ω (⊃E (DAB ω) DA))))

   -- Negation in CPL
   validaxioms □N con = ⊃I (⊃I (□E (hyp Z) 
      λ DA → ¬□E (hyp (S Z)) 
      λ ω ¬DA → abort (¬DA (DA ω))))
   validaxioms ◇N con = ⊃I (⊃I (◇E (hyp Z)
      λ ω DA → ¬◇E (hyp (S Z))
      λ ¬DA → abort (¬DA ω DA)))
   validaxioms □C con =
      ⊃I (□E (hyp Z) (λ D → ¬◇I (λ ω D0 → con ω (⊃E D0 (D ω)))))
   validaxioms ◇C con = 
      ⊃I (◇E (hyp Z) (λ ω D → ¬□I ω (λ D' → con ω (⊃E D' D))))



   -- Valid axioms in a transitive accessibility relation
   validtrans : ∀{Γ A w} 
      → Trans
      → (∀ {w'} → w ≺ w' → Γ ⊢ ⊥ [ w ] → Void) 
      → TransAxiom A 
      → Γ ⊢ A [ w ]
   validtrans _≺≺_ con □4 = ⊃I (□E (hyp Z) 
      λ D → □I λ ω → □I λ ω' → D (ω ≺≺ ω'))
   validtrans _≺≺_ con (GL {A}) = ind P lemma _
    where
      P : W → Set
      P = λ w → ∀{Γ} → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   
      lemma : (w : W) → ((w' : W) → w ≺ w' → P w') → P w
      lemma w ih = ⊃I (□E (hyp Z) 
         λ DInd → □I 
         λ ω → ⊃E (DInd ω) (⊃E (ih _ ω) (□I (λ ω' → DInd (ω ≺≺ ω')))))


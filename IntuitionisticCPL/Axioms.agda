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
   demorgan2 : ∀{Γ A w} 
      → Con Γ w 
      → Γ ⊢ ◇ (¬ A) ⊃ ¬ (□ A) [ w ]
   demorgan2 con = ⊃I {!!}
   

module NON-AXIOMS where
   open TRANS-UWF Example
   open PROPERTIES Example
   open ILIST Example
   open CORE Example
   open SEQUENT Example
   open EQUIV Example

{-
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
-}




module SOUNDNESS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open PROPERTIES UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF
   open EQUIV UWF

{-
   -- Valid Axioms
   I : ∀{Γ A w} 
      → Γ ⊢ A ⊃ A [ w ]
   I = 


   -- Axioms of IK, Simpson's intuitionstic modal logic (Theorem 3.3)
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

-}

module NOT-4□ where
   open TRANS-UWF Example
   open PROPERTIES Example
   open ILIST Example
   open CORE Example
   open SEQUENT Example
   open EQUIV Example

   Q : Type
   Q = a "Q"   

   4□ : [] ⇒ ◇ (◇ Q) ⊃ ◇ Q [ α ] → Void
   4□ (⊃L () _ _)
   4□ (⊥L ()) 
   4□ (◇L () _)
   4□ (□L () _)
   4□ (¬◇L () _) 
   4□ (¬□L () _) 
   4□ (⊃R D) = {!!}
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

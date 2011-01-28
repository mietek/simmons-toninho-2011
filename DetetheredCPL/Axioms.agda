-- Constructive Provability Logic 
-- De-tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Valid and invalid axioms

module DetetheredCPL.Axioms where
open import Prelude hiding (⊥ ; ¬)
open import Accessibility.Inductive
open import Accessibility.Five
open import Accessibility.IndexedList
open import DetetheredCPL.Core
open import DetetheredCPL.Sequent
open import DetetheredCPL.Equiv

Ctx = List Type

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

module AXIOMS (UWF : UpwardsWellFounded 
   ; dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
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
   ax⊥E = ⊃I (⊥E ≺*≡ (hyp Z))

 -- Necessitation rule (Theorem 3.2)
   Nec : ∀{Γ A} 
      → (∀{w} → Γ ⊢ A [ w ])
      → (∀{w} → Γ ⊢ □ A [ w ])
   Nec D = □I (λ ω → D) 
    
 -- Axioms of IK, Simpson's intuitionistic modal logic (Theorem 3.3)
   axK□ : ∀{Γ A B w}
      → Γ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B [ w ]
   axK□ = ⊃I (⊃I (□E ≺*≡ (hyp (S Z)) 
      (λ D₀ → □E ≺*≡ (hyp Z) 
      (λ D₀' → □I (λ ω → ⊃E (D₀ ω) (D₀' ω))))))

   axK◇ : ∀{Γ A B w}
      → Γ ⊢ □ (A ⊃ B) ⊃ ◇ A ⊃ ◇ B [ w ]
   axK◇ = ⊃I (⊃I (◇E ≺*≡ (hyp Z) 
      (λ ω D₀ → □E ≺*≡ (hyp (S Z)) 
      (λ D₀' → ◇I ω (⊃E (D₀' ω) D₀)))))

   ax4□ : ∀{Γ A w}
      → Trans
      → Γ ⊢ □ A ⊃ □ (□ A) [ w ]
   ax4□ _≺≺_ = ⊃I (□E ≺*≡ (hyp Z) 
      λ D → □I λ ω → □I λ ω' → D (ω ≺≺ ω'))
 

   ax◇⊥ : ∀{Γ w}
      → Γ ⊢ ¬ (◇ ⊥) [ w ]
   ax◇⊥ = ⊃I (◇E ≺*≡ (hyp Z) 
      (λ ω D₀ → ⊥E (≺*+ (≺+0 ω)) D₀))


   ax4◇ : ∀{Γ A w}
      → Trans
      → Γ ⊢ ◇ (◇ A) ⊃ ◇ A [ w ]
   ax4◇  _≺≺_ = ⊃I (◇E ≺*≡ (hyp Z) 
      (λ ω D₀ → ◇E (≺*+ (≺+0 ω)) D₀ 
      (λ ω' D₀' → ◇I (ω ≺≺ ω') D₀')))

   
   
 -- Provability logic (Theorem 3.4)
   axGL : ∀{Γ A w}
      → Trans
      → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   axGL {A = A} _≺≺_ = ind P lemma _
    where
      P : W → Set
      P = λ w → ∀{Γ} → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   
      lemma : (w : W) → ((w' : W) → w ≺ w' → P w') → P w
      lemma w ih = ⊃I (□E ≺*≡ (hyp Z) 
         λ DInd → □I 
         λ ω → ⊃E (DInd ω) (⊃E (ih _ ω) (□I (λ ω' → DInd (ω ≺≺ ω')))))

   -- Löb rule (Theorem 3.5)
  

   Löb : ∀{Γ A}
      → (∀{w} → Γ ⊢ □ A ⊃ A [ w ])
      → (∀{w} → Γ ⊢ A [ w ])
   Löb {Γ} {A} D = {!!}



   -- De Morgan dualities (Theorem 3.6)
   ax◇¬ : ∀{Γ A w}  
      → Γ ⊢ ◇ (¬ A) ⊃ ¬ (□ A) [ w ]
   ax◇¬  = ⊃I (⊃I (□E ≺*≡ (hyp Z) 
      (λ D₀ → ◇E ≺*≡ (hyp (S Z)) 
      (λ ω D₀' → ⊥E (≺*+ (≺+0 ω)) (⊃E D₀' (D₀ ω))))))


   ax□¬ : ∀{Γ A w} 
      → Γ ⊢ □ (¬ A) ⊃ ¬ (◇ A) [ w ]
   ax□¬ = ⊃I (⊃I (◇E ≺*≡ (hyp Z) 
      (λ ω D₀ → □E ≺*≡ (hyp (S Z)) 
      (λ D₀' → ⊥E (≺*+ (≺+0 ω)) (⊃E (D₀' ω) D₀)))))

module NON-AXIOMS where
   open TRANS-UWF Example
   open PROPERTIES Example
   open ILIST Example
   open CORE Example
   open SEQUENT Example
   open EQUIV Example

   Q : Type
   Q = a "Q"   


   deMorgan2 : [] ⇒ ¬ (□ Q) ⊃ ◇ (¬ Q) [ β ] → Void
   deMorgan2 = lem0
    where

      lem2 : ((□ Q ⊃ ⊥) at β :: []) ⇒ Q [ δ ] → Void
      lem2 (hyp (S ())) 
      lem2 (⊃L (≺*+ (≺+0 ())) Z D₁ D₂)
      lem2 (⊃L (≺*+ (≺+S () y')) Z D₁ D₂)
      lem2 (⊃L ωh (S ()) D₁ D₂)
      lem2 (⊥L ωh (S ()))
      lem2 (◇L ωh (S ()) D₁)
      lem2 (□L ωh (S ()) D₁) 

      lem1 : (□ Q ⊃ ⊥) at β :: [] ⇒ (□ Q) [ β ] → Void
      lem1 (⊃L ωh Z D₁ D₂) = lem1 D₁
      lem1 (⊃L ωh (S ()) D₁ D₂)
      lem1 (⊥L ωh (S ()))
      lem1 (◇L ωh (S ()) D₁)
      lem1 (□R D₁) = lem2 (D₁ Z)
      lem1 (□L ωh (S ()) D₁)
      
      lem0 : [] ⇒ ¬ (□ Q) ⊃ ◇ (¬ Q) [ β ] → Void
      lem0 (⊃R (⊃L ωh Z D₁ D₂)) = lem1 D₁
      lem0 (⊃R (⊃L ωh (S ()) D₁ D₂))
      lem0 (⊃R (⊥L ωh (S ())))
      lem0 (⊃R (◇R Z (⊃R (⊃L (≺*+ (≺+0 ())) (S Z) D₁ D₂))))
      lem0 (⊃R (◇R Z (⊃R (⊃L (≺*+ (≺+S () y')) (S Z) D₁ D₂))))
      lem0 (⊃R (◇R Z (⊃R (⊃L ωh (S (S ())) D₁ D₂))))
      lem0 (⊃R (◇R Z (⊃R (⊥L ωh (S (S ()))))))
      lem0 (⊃R (◇R Z (⊃R (◇L ωh (S (S ())) D₁))))
      lem0 (⊃R (◇R Z (⊃R (□L ωh (S (S ())) D₁))))
      lem0 (⊃R (◇R Z (⊃L (≺*+ (≺+0 ())) Z D₁ D₂)))
      lem0 (⊃R (◇R Z (⊃L (≺*+ (≺+S () y')) Z D₁ D₂)))
      lem0 (⊃R (◇R Z (⊃L ωh (S ()) D₁ D₂)))
      lem0 (⊃R (◇R Z (⊥L ωh (S ()))))
      lem0 (⊃R (◇R Z (◇L ωh (S ()) D₁)))
      lem0 (⊃R (◇R Z (□L ωh (S ()) D₁)))
      lem0 (⊃R (◇R (S ()) D₁))
      lem0 (⊃R (◇L ωh (S ()) D₁))
      lem0 (⊃R (□L ωh (S ()) D₁))
      lem0 (⊃L ωh () D₁ D₂)
      lem0 (⊥L ωh ())
      lem0 (◇L ωh () D₁)
      lem0 (□L ωh () D₁)


   deMorgan1 : [] ⇒ ¬ (◇ Q) ⊃ □(¬ Q) [ β ] → Void
   deMorgan1 = lem0
    where
      lem2 : ( (◇ Q ⊃ ⊥) at β :: []) ⇒ (◇ Q) [ β ] → Void
      lem2 (⊃L ωh Z D₁ D₂) = lem2 D₁
      lem2 (⊃L ωh (S ()) D₁ D₂)
      lem2 (⊥L ωh (S ()))
      lem2 (CORE.◇R Z (hyp (S ()))) 
      lem2 (CORE.◇R Z (⊃L (≺*+ (≺+0 ())) Z D₁ D₂)) 
      lem2 (CORE.◇R Z (⊃L (≺*+ (≺+S () y')) Z D₁ D₂))
      lem2 (CORE.◇R Z (⊃L ωh (S ()) D₁ D₂))
      lem2 (CORE.◇R Z (⊥L ωh (S ()))) 
      lem2 (CORE.◇R Z (◇L ωh (S ()) D₁)) 
      lem2 (CORE.◇R Z (□L ωh (S ()) D₁)) 
      lem2 (◇R (S ()) D₁)
      lem2 (◇L ωh (S ()) D₁)
      lem2 (□L ωh (S ()) D₁) 

      lem1 : ((◇ Q ⊃ ⊥) at β :: []) ⇒ (a "Q" ⊃ ⊥) [ δ ] → Void
      lem1 (⊃R (⊃L (≺*+ (≺+0 ())) (S Z) D₁ D₂))
      lem1 (⊃R (⊃L (≺*+ (≺+S () y')) (S Z) D₁ D₂))
      lem1 (⊃R (⊃L ωh (S (S ())) D₁ D₂))
      lem1 (⊃R (⊥L ωh (S (S ()))))
      lem1 (⊃R (◇L ωh (S (S ())) D₁))
      lem1 (⊃R (□L ωh (S (S ())) D₁))
      lem1 (⊃L (≺*+ (≺+0 ())) Z D₁ D₂)
      lem1 (⊃L (≺*+ (≺+S () y')) Z D₁ D₂)
      lem1 (⊃L ωh (S ()) D₁ D₂)
      lem1 (⊥L ωh (S ()))
      lem1 (◇L ωh (S ()) D₁)
      lem1 (□L ωh (S ()) D₁)
          
      lem0 : [] ⇒ ¬ (◇ Q) ⊃ □(¬ Q) [ β ] → Void
      lem0 (⊃R (⊃L ωh Z D₁ D₂)) = lem2 D₁
      lem0 (⊃R (⊃L ωh (S ()) D₁ D₂))
      lem0 (⊃R (⊥L ωh (S ())))
      lem0 (⊃R (◇L ωh (S ()) D₁))
      lem0 (⊃R (□R D₁)) = lem1 (D₁ Z)
      lem0 (⊃R (□L ωh (S ()) D₁))
      lem0 (⊃L ωh () D₁ D₂) 
      lem0 (⊥L ωh ())
      lem0 (◇L ωh () D₁) 
      lem0 (□L ωh () D₁) 


   
   axIK : [] ⇒ (◇ Q ⊃ □ ⊥) ⊃ □ (Q ⊃ ⊥) [ β ] → Void
   axIK = lem0
    where
       lem2 : ((◇ Q ⊃ □ ⊥) at β :: []) ⇒ (Q ⊃ ⊥) [ δ ] → Void
       lem2 (⊃R (⊃L (≺*+ (≺+0 ())) (S Z) D₁ D₂))
       lem2 (⊃R (⊃L (≺*+ (≺+S () y')) (S Z) D₁ D₂))
       lem2 (⊃R (⊃L ωh (S (S ())) D₁ D₂))
       lem2 (⊃R (⊥L ωh (S (S ()))))
       lem2 (⊃R (◇L ωh (S (S ())) D₁)) 
       lem2 (⊃R (□L ωh (S (S ())) D₁)) 
       lem2 (⊃L (≺*+ (≺+0 ())) Z D₁ D₂)
       lem2 (⊃L (≺*+ (≺+S () y')) Z D₁ D₂)
       lem2 (⊃L ωh (S ()) D₁ D₂)
       lem2 (⊥L ωh (S ()))
       lem2 (◇L ωh (S ()) D₁)
       lem2 (□L ωh (S ()) D₁)
     
       lem1 : ((◇ Q) ⊃ □ ⊥) at β :: [] ⇒ (◇ Q) [ β ] → Void
       lem1 (⊃L ωh' Z D₁' D₂) = lem1 D₁'
       lem1 (⊃L ωh' (S ()) D₁' D₂)
       lem1 (⊥L ωh' (S ())) 
       lem1 (◇R Z (hyp (S ())))
       lem1 (◇R Z (⊃L (≺*+ (≺+0 ())) Z D₁ D₂))
       lem1 (◇R Z (⊃L (≺*+ (≺+S () y')) Z D₁ D₂))
       lem1 (◇R Z (⊃L ωh (S ()) D₁ D₂))
       lem1 (◇R Z (⊥L ωh (S ()))) 
       lem1 (◇R Z (◇L ωh (S ()) D₁)) 
       lem1 (◇R Z (□L ωh (S ()) D₁)) 
       lem1 (◇R (S ()) D₁')
       lem1 (◇L ωh' (S ()) D₁')
       lem1 (□L ωh' (S ()) D₁') 

       lem0 : [] ⇒ (◇ Q ⊃ □ ⊥) ⊃ □ (Q ⊃ ⊥) [ β ] → Void
       lem0 (⊃R (⊃L ωh Z D₁ D₂)) = lem1 D₁
       lem0 (⊃R (⊃L ωh (S ()) D₁ D₂))
       lem0 (⊃R (⊥L ωh (S ())))
       lem0 (⊃R (◇L ωh (S ()) D₁))
       lem0 (⊃R (□R D₁)) = lem2 (D₁ Z)
       lem0 (⊃R (□L ωh (S ()) D₁))
       lem0 (⊃L ωh () D₁ D₂)
       lem0 (⊥L ωh ())
       lem0 (◇L ωh () D₁) 
       lem0 (□L ωh () D₁)



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


module AXIOMS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open PROPERTIES UWF
   open ILIST UWF
   open CORE UWF 
   
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
   Löb D = ind LöbP Löb' _ D
    where 
      LöbP : W → Set
      LöbP = λ w → ∀{Γ A} → (∀{w} → Γ ⊢ (□ A) ⊃ A [ w ]) → Γ ⊢ A [ w ]

      Löb' : (w : W) → ((w' : W) → w ≺ w' → LöbP w') → LöbP w
      Löb' w ih D = ⊃E D (□I (λ ω → ih _ ω D))

 -- De Morgan laws (Theorem 3.6)
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
  

   Q : Type
   Q = a "Q"   


   deMorgan2 : [] ⇒ ¬ (□ Q) ⊃ ◇ (¬ Q) [ β ] → Void
   deMorgan2 = lem0
    where

      lem2 : (¬ (□ Q) at β :: []) ⇒ Q [ δ ] → Void
      lem2 (hyp (S ())) 
      lem2 (⊃L (≺*+ (≺+0 ())) Z _ _)
      lem2 (⊃L (≺*+ (≺+S () _)) Z _ _)
      lem2 (⊃L _ (S ()) _ _)
      lem2 (⊥L _ (S ()))
      lem2 (◇L _ (S ()) _)
      lem2 (□L _ (S ()) _) 

      lem1 : (¬ (□ Q)) at β :: [] ⇒ (□ Q) [ β ] → Void
      lem1 (⊃L _ Z D₁ _) = lem1 D₁
      lem1 (⊃L _ (S ()) _ _)
      lem1 (⊥L _ (S ()))
      lem1 (◇L _ (S ()) _)
      lem1 (□R D₁) = lem2 (D₁ Z)
      lem1 (□L _ (S ()) _)
      
      lem0 : [] ⇒ ¬ (□ Q) ⊃ ◇ (¬ Q) [ β ] → Void
      lem0 (⊃R (⊃L _ Z D₁ _)) = lem1 D₁
      lem0 (⊃R (⊃L _ (S ()) _ _))
      lem0 (⊃R (⊥L _ (S ())))
      lem0 (⊃R (◇R Z (⊃R (⊃L (≺*+ (≺+0 ())) (S Z) _ _))))
      lem0 (⊃R (◇R Z (⊃R (⊃L (≺*+ (≺+S () _)) (S Z) _ _))))
      lem0 (⊃R (◇R Z (⊃R (⊃L _ (S (S ())) _ _))))
      lem0 (⊃R (◇R Z (⊃R (⊥L _ (S (S ()))))))
      lem0 (⊃R (◇R Z (⊃R (◇L _ (S (S ())) _))))
      lem0 (⊃R (◇R Z (⊃R (□L _ (S (S ())) _))))
      lem0 (⊃R (◇R Z (⊃L (≺*+ (≺+0 ())) Z _ _)))
      lem0 (⊃R (◇R Z (⊃L (≺*+ (≺+S () _)) Z _ _)))
      lem0 (⊃R (◇R Z (⊃L _ (S ()) _ _)))
      lem0 (⊃R (◇R Z (⊥L _ (S ()))))
      lem0 (⊃R (◇R Z (◇L _ (S ()) _)))
      lem0 (⊃R (◇R Z (□L _ (S ()) _)))
      lem0 (⊃R (◇R (S ()) _))
      lem0 (⊃R (◇L _ (S ()) _))
      lem0 (⊃R (□L _ (S ()) _))
      lem0 (⊃L _ () _ _)
      lem0 (⊥L _ ())
      lem0 (◇L _ () _)
      lem0 (□L _ () _)


   deMorgan1 : [] ⇒ ¬ (◇ Q) ⊃ □(¬ Q) [ β ] → Void
   deMorgan1 = lem0
    where
      lem2 : ( ¬ (◇ Q) at β :: []) ⇒ (◇ Q) [ β ] → Void
      lem2 (⊃L _ Z D₁ _) = lem2 D₁
      lem2 (⊃L _ (S ()) _ _)
      lem2 (⊥L _ (S ()))
      lem2 (◇R Z (hyp (S ()))) 
      lem2 (◇R Z (⊃L (≺*+ (≺+0 ())) Z _ _)) 
      lem2 (◇R Z (⊃L (≺*+ (≺+S () _)) Z _ _))
      lem2 (◇R Z (⊃L _ (S ()) _ _))
      lem2 (◇R Z (⊥L _ (S ()))) 
      lem2 (◇R Z (◇L _ (S ()) _)) 
      lem2 (◇R Z (□L _ (S ()) _)) 
      lem2 (◇R (S ()) _)
      lem2 (◇L _ (S ()) _)
      lem2 (□L _ (S ()) _) 

      lem1 : (¬ (◇ Q) at β :: []) ⇒ (¬ Q) [ δ ] → Void
      lem1 (⊃R (⊃L (≺*+ (≺+0 ())) (S Z) _ _))
      lem1 (⊃R (⊃L (≺*+ (≺+S () y')) (S Z) _ _ ))
      lem1 (⊃R (⊃L _ (S (S ())) _ _ ))
      lem1 (⊃R (⊥L _ (S (S ()))))
      lem1 (⊃R (◇L _ (S (S ())) _))
      lem1 (⊃R (□L _ (S (S ())) _))
      lem1 (⊃L (≺*+ (≺+0 ())) Z _ _)
      lem1 (⊃L (≺*+ (≺+S () _)) Z _ _)
      lem1 (⊃L _ (S ()) _ _)
      lem1 (⊥L _ (S ()))
      lem1 (◇L _ (S ()) _)
      lem1 (□L _ (S ()) _)
          
      lem0 : [] ⇒ ¬ (◇ Q) ⊃ □(¬ Q) [ β ] → Void
      lem0 (⊃R (⊃L _ Z D₁ _)) = lem2 D₁
      lem0 (⊃R (⊃L _ (S ()) _ _))
      lem0 (⊃R (⊥L _ (S ())))
      lem0 (⊃R (◇L _ (S ()) _))
      lem0 (⊃R (□R D₁)) = lem1 (D₁ Z)
      lem0 (⊃R (□L _ (S ()) _))
      lem0 (⊃L _ () _ _) 
      lem0 (⊥L _ ())
      lem0 (◇L _ () _) 
      lem0 (□L _ () _) 


   
   axIK : [] ⇒ (◇ Q ⊃ □ ⊥) ⊃ □ (Q ⊃ ⊥) [ β ] → Void
   axIK = lem0
    where
       lem2 : ((◇ Q ⊃ □ ⊥) at β :: []) ⇒ (Q ⊃ ⊥) [ δ ] → Void
       lem2 (⊃R (⊃L (≺*+ (≺+0 ())) (S Z) _ _))
       lem2 (⊃R (⊃L (≺*+ (≺+S () _)) (S Z) _ _))
       lem2 (⊃R (⊃L _ (S (S ())) _ _))
       lem2 (⊃R (⊥L _ (S (S ()))))
       lem2 (⊃R (◇L _ (S (S ())) _)) 
       lem2 (⊃R (□L _ (S (S ())) _)) 
       lem2 (⊃L (≺*+ (≺+0 ())) Z _ _)
       lem2 (⊃L (≺*+ (≺+S () y')) Z _ _)
       lem2 (⊃L _ (S ()) _ _)
       lem2 (⊥L _ (S ()))
       lem2 (◇L _ (S ()) _)
       lem2 (□L _ (S ()) _)
     
       lem1 : ((◇ Q) ⊃ □ ⊥) at β :: [] ⇒ (◇ Q) [ β ] → Void
       lem1 (⊃L _ Z D₁' _) = lem1 D₁'
       lem1 (⊃L _ (S ()) _ _)
       lem1 (⊥L _ (S ())) 
       lem1 (◇R Z (hyp (S ())))
       lem1 (◇R Z (⊃L (≺*+ (≺+0 ())) Z _ _))
       lem1 (◇R Z (⊃L (≺*+ (≺+S () _)) Z _ _))
       lem1 (◇R Z (⊃L _ (S ()) _ _))
       lem1 (◇R Z (⊥L _ (S ()))) 
       lem1 (◇R Z (◇L _ (S ()) _)) 
       lem1 (◇R Z (□L _ (S ()) _)) 
       lem1 (◇R (S ()) _)
       lem1 (◇L _ (S ()) _)
       lem1 (□L _ (S ()) _) 

       lem0 : [] ⇒ (◇ Q ⊃ □ ⊥) ⊃ □ (Q ⊃ ⊥) [ β ] → Void
       lem0 (⊃R (⊃L _ Z D₁ _)) = lem1 D₁
       lem0 (⊃R (⊃L _ (S ()) _ _))
       lem0 (⊃R (⊥L _ (S ())))
       lem0 (⊃R (◇L _ (S ()) _))
       lem0 (⊃R (□R D₁)) = lem2 (D₁ Z)
       lem0 (⊃R (□L _ (S ()) _))
       lem0 (⊃L _ () _ _)
       lem0 (⊥L _ ())
       lem0 (◇L _ () _) 
       lem0 (□L _ () _)



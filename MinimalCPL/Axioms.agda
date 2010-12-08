-- Constructive Provability Logic 
-- The minimal, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

module MinimalCPL.Axioms where
open import Prelude
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import MinimalCPL.Core
open import MinimalCPL.Sequent

module AXIOMS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF

   Trans : Set
   Trans = ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃

   infix 4 ⊩_
   ⊩_ : Type → Set
   ⊩ A = ∀{Γ w} → Γ ⊢ A [ w ]

   -- Minimal logic
   MP : ∀{A B} → ⊩ A ⊃ B → ⊩ A → ⊩ B
   MP DAB DA = ⊃E DAB DA

   axI : ∀{A} → ⊩ A ⊃ A 
   axI = ⊃I (hyp Z)

   axS : ∀{A B} → ⊩ A ⊃ B ⊃ A 
   axS = ⊃I (⊃I (hyp (S Z)))

   axK : ∀{A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ (A ⊃ C) 
   axK = ⊃I (⊃I (⊃I (⊃E (⊃E (hyp (S (S Z))) (hyp Z)) (⊃E (hyp (S Z)) (hyp Z)))))

   -- Modal logic
   Nec : ∀{A} → ⊩ A → ⊩ □ A
   Nec D = □I (λ ω → D)

   axK□ : ∀{A B} → ⊩ □ (A ⊃ B) ⊃ (□ A ⊃ □ B)
   axK□ = ⊃I (⊃I (□E (hyp (S Z))
      λ DAB → □E (hyp Z) 
      λ DA → □I (λ ω → ⊃E (DAB ω) (DA ω))))
   
   axK◇ : ∀{A B} → ⊩ □ (A ⊃ B) ⊃ (◇ A ⊃ ◇ B) 
   axK◇ = ⊃I (⊃I (□E (hyp (S Z)) 
      λ DAB → ◇E (hyp Z) 
      λ ω DA → ◇I ω (⊃E (DAB ω) DA)))

   -- Negated modal connectives
   axN□ : ∀{A B} → ⊩ ¬□ A ⊃ □ A ⊃ B 
   axN□ = ⊃I (⊃I (□E (hyp Z) 
      λ DA → ¬□E (hyp (S Z)) 
      λ ω ¬DA → abort (¬DA (DA ω))))

   axN◇ : ∀{A B} → ⊩ ¬◇ A ⊃ ◇ A ⊃ B 
   axN◇ = ⊃I (⊃I (◇E (hyp Z)
      λ ω DA → ¬◇E (hyp (S Z))
      λ ¬DA → abort (¬DA ω DA)))

   -- Provability logic
   LöbP : W → Set
   LöbP = λ w → ∀{Γ A} → ⊩ □ A ⊃ A → Γ ⊢ A [ w ]

   Löb' : (w : W) → ((w' : W) → w ≺ w' → LöbP w') → LöbP w
   Löb' w ih D = ⊃E D (□I (λ ω → ih _ ω D))

   Löb : ∀{A} → ⊩ □ A ⊃ A → ⊩ A
   Löb D = ind LöbP Löb' _ D

   axGLP : W → Set
   axGLP = λ w → ∀{Γ A} → Trans → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   
   axGL' : (w : W) → ((w' : W) → w ≺ w' → axGLP w') → axGLP w
   axGL' w ih _≺≺_ = ⊃I (□E (hyp Z) 
      λ DInd → □I 
      λ ω → ⊃E (DInd ω) (⊃E (ih _ ω _≺≺_) (□I (λ ω' → DInd (ω ≺≺ ω')))))

   axGL : ∀{A} → Trans → ⊩ □ (□ A ⊃ A) ⊃ □ A 
   axGL _≺≺_ = ind axGLP axGL' _ _≺≺_

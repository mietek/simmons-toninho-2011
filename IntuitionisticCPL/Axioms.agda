-- Constructive Provability Logic 
-- The intuitionistic, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Valid and invalid axioms

module IntuitionisticCPL.Axioms where
open import Prelude hiding (⊥ ; ¬)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import IntuitionisticCPL.Core
open import IntuitionisticCPL.Sequent
open import IntuitionisticCPL.Equiv

Ctx = List Type

¬ : Type → Type
¬ A = A ⊃ ⊥

module HILBERT where
   -- True in any instantiation of CPL
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
      □C' : ∀{A} → Axiom (¬◇ (A ⊃ ⊥) ⊃ □ A)

   -- True in any transitive instantiation of CPL
   data TransAxiom : Type → Set where
      □4 : ∀{A} → TransAxiom (□ A ⊃ □ (□ A))
      GL : ∀{A} → TransAxiom (□ (□ A ⊃ A) ⊃ □ A)

   -- False in any model
   data Counter : Type → Set where
      ◇4 : ∀{A} → Counter (◇ (◇ A) ⊃ ◇ A)

   data _⊩_ : Ctx → Type → Set where

module SOUNDNESS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF
   open EQUIV UWF
   open HILBERT

   Trans : Set
   Trans = ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃

   Con : MCtx → W → Set
   Con Γ w = ∀ {w'} → w ≺ w' → Γ ⇒ ⊥ [ w' ] → Void

   Empty : MCtx → W → Set
   Empty Γ w = ∀ {A} → A at w ∈ Γ → Void

   Dec : MCtx → Type → W → Set
   Dec Γ A w = ∀ {w' Γ} → w ≺ w' → Decidable (Γ ⊢ A [ w' ])


  
   -- De Morgan's laws
   DProc¬□ : MCtx → Type → W → Set
   DProc¬□ Γ A w = Sum 
      (∀ {w'} → w ≺ w' → Γ ⇒ A [ w' ])
      (∃ λ w' → (w ≺ w') × (Γ ⇒ ¬ A [ w' ]))

   DProc□n : MCtx → Type → W → Set
   DProc□n Γ A w = Sum 
      (∀ {w'} → w ≺ w' → Γ ⇒ A [ w' ])
      (∃ λ w' → (w ≺ w') × ((Γ ⇒ A [ w' ]) → Void) )

   DProc¬◇ : MCtx → Type → W → Set
   DProc¬◇ Γ A w = Sum 
      (∀ {w'} → w ≺ w' → Γ ⇒ ¬ A [ w' ])
      (∃ λ w' → (w ≺ w') × (Γ ⇒ A [ w' ]))

   demorgan1 : ∀{Γ A w} 
      → Empty Γ w 
      → Equiv (DProc¬□ Γ A w) (Γ ⇒ ¬ (□ A) ⊃ ◇ (¬ A) [ w ])
   demorgan1 {Γ} {A} {w} emp = forward , back2 
    where 
      forward : DProc¬□ Γ A w → Γ ⇒ ¬ (□ A) ⊃ ◇ (¬ A) [ w ]
      forward (Inl D) = ⊃R (⊃L Z (□R 
         λ ω → wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (D ω)) (⊥L Z))
      forward (Inr (w , ω , D⊥)) = 
         ⊃R (◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D⊥))

      back0 : ¬ (□ A) at w :: Γ ⇒ □ A [ w ] → DProc¬□ Γ A w
      back0 (□R D) = Inl (λ ω → wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω))
      back0 (⊃L Z D _) = back0 D
      back0 (⊃L (S n) _ _) = abort (emp n)
      back0 (⊥L (S n)) = abort (emp n)
      back0 (◇L (S n) _) = abort (emp n)
      back0 (□L (S n) _) = abort (emp n)
      back0 (¬◇L (S n) _) = abort (emp n)
      back0 (¬□L (S n) _) = abort (emp n)

      back1 : ¬ (□ A) at w :: Γ ⇒ ◇ (¬ A) [ w ] → DProc¬□ Γ A w
      back1 (⊃L Z D _) = back0 D
      back1 (◇R ω D⊥) = Inr (_ , ω , wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D⊥)
      back1 (⊃L (S n) _ _) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇L (S n) _) = abort (emp n)
      back1 (□L (S n) _) = abort (emp n)
      back1 (¬◇L (S n) _) = abort (emp n)
      back1 (¬□L (S n) _) = abort (emp n)

      back2 : Γ ⇒ ¬ (□ A) ⊃ ◇ (¬ A) [ w ] → DProc¬□ Γ A w
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n)

   demorgan2 : ∀{Γ A w} → Con Γ w → Γ ⇒ ◇ (¬ A) ⊃ ¬ (□ A) [ w ]
   demorgan2 con = ⊃R (◇L Z 
      λ ω D⊥ → ⊃R (□L Z 
      λ D → abort (con ω (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (nd→seq 
       (⊃E (seq→nd D⊥) 
        (seq→nd (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω)))))))))

  

   demorgan3 : ∀{Γ A w}
            → Empty Γ w
            → Equiv (DProc¬◇ Γ A w) (Γ ⇒ ¬ (◇ A) ⊃ □ (¬ A) [ w ])
   demorgan3 {Γ} {A} {w} emp = forward , back2
    where
      forward : (DProc¬◇ Γ A w) → (Γ ⇒ ¬ (◇ A) ⊃ □ (¬ A) [ w ])
      forward (Inl D⊥) = 
         ⊃R (□R (λ ω → wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (D⊥ ω)))
      forward (Inr (w₀ , ω , D)) = 
         ⊃R (⊃L Z (◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D)) (⊥L Z))

      back : (◇ A ⊃ ⊥) at w :: Γ ⇒ ◇ A [ w ] → DProc¬◇ Γ A w
      back (⊃L Z D _) = back D
      back (⊃L (S n) _ _) = abort (emp n)
      back (⊥L (S n)) = abort (emp n)
      back (◇R ω D) = Inr (_ , ω , wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D)
      back (◇L (S n) _) = abort (emp n)
      back (□L (S n) _) = abort (emp n)
      back (¬◇L (S n) _) = abort (emp n)
      back (¬□L (S n) _) = abort (emp n)

      back1 : (◇ A ⊃ ⊥) at w :: Γ ⇒ □ (A ⊃ ⊥) [ w ] → DProc¬◇ Γ A w
      back1 (⊃L Z D _) = back D
      back1 (⊃L (S n) _ _) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇L (S n) _) = abort (emp n)
      back1 (□R D) = Inl (λ ω → wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω))
      back1 (□L (S n) _) = abort (emp n)
      back1 (¬◇L (S n) _) = abort (emp n)
      back1 (¬□L (S n) _) = abort (emp n)
       
      back2 : Γ ⇒ ¬ (◇ A) ⊃ □ (¬ A) [ w ] → DProc¬◇ Γ A w
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n)

   demorgan4 : ∀{Γ A w} → Con Γ w → Γ ⇒ □ (¬ A) ⊃ ¬ (◇ A) [ w ]
   demorgan4 con = ⊃R (⊃R (◇L Z (λ ω D → □L (S Z) 
      λ D₀ → abort (con ω (nd→seq (⊃E 
       (seq→nd (wk (⊆to/irrev (≺⊀ ω) (⊆to/irrev (≺⊀ ω) (⊆to/refl _))) 
        (D₀ ω))) 
       (seq→nd (wk (⊆to/irrev (≺⊀ ω) (⊆to/irrev (≺⊀ ω) (⊆to/refl _))) 
        D))))))))


   □n : ∀{Γ A w} 
            → Empty Γ w
            → Equiv (DProc□n Γ A w) (Γ ⇒ ¬ (□ A) ⊃ ¬□ A [ w ])
   □n {Γ} {A} {w} emp = forward , back2
    where
      forward : (DProc□n Γ A w) → (Γ ⇒ ¬ (□ A) ⊃ ¬□ A [ w ])
      forward (Inl D) = ⊃R (⊃L Z (□R (λ ω → wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (D ω))) (⊥L Z))
      forward (Inr (w₀ , ω , DV)) = ⊃R (¬□R ω (λ D → DV (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D)))

      back : (□ A ⊃ ⊥) at w :: Γ ⇒ □ A [ w ] → (DProc□n Γ A w)
      back (⊃L Z y' y0) = back y'
      back (⊃L (S n) y' y0) = abort (emp n)
      back (⊥L (S n)) = abort (emp n)
      back (◇L (S n) y') = abort (emp n)
      back (□R D) = Inl (λ ω → wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω))
      back (□L (S n) y') = abort (emp n)
      back (¬◇L (S n) y') = abort (emp n)
      back (¬□L (S n) y') = abort (emp n) 

      back1 : (□ A ⊃ ⊥) at w :: Γ ⇒ ¬□ A [ w ] → (DProc□n Γ A w)
      back1 (⊃L Z y' y0) = back y'
      back1 (⊃L (S n) y' y0) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇L (S n) y') = abort (emp n)
      back1 (□L (S n) y') = abort (emp n)
      back1 (¬◇L (S n) y') = abort (emp n)
      back1 (¬□R ω D) = Inr (_ , (ω , (λ D₀ → D (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D₀))))
      back1 (¬□L (S n) y') = abort (emp n) 

      back2 : (Γ ⇒ ¬ (□ A) ⊃ ¬□ A [ w ]) → (DProc□n Γ A w)
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n) 


   ◇c : ∀{Γ A w} 
            → Empty Γ w
            → Equiv (DProc□n Γ A w) (Γ ⇒ ¬□ (¬ A) ⊃ ◇ A [ w ])

   ◇c {Γ} {A} {w} emp = {!!} , {!!} 
    where
      forward : (DProc¬□ Γ A w) → (Γ ⇒ ¬□ (¬ A) ⊃ ◇ A [ w ])
      forward (Inl inl) = ⊃R (¬□L Z (λ ω D₀ → ◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (inl ω))))
      forward (Inr (w₀ , ω , DV)) = ⊃R (¬□L Z (λ ω' D₀ → {!!})) 



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
   validaxioms □C con = ⊃I (□E (hyp Z) (λ D → ¬◇I (λ ω D0 → con ω (⊃E D0 (D ω)))))
   validaxioms ◇C con = ⊃I (◇E (hyp Z) (λ ω D → ¬□I ω (λ D' → con ω (⊃E D' D))))

   validaxioms □C' con = ⊃I (¬◇E (hyp Z) (λ D → □I (λ ω → {!!})))

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

data Hilbert : Bool → Ctx → Type → Set where
   


mutual
   infix 4 _⊩_
   infix 4 _⊪_

   _⊩_ : Ctx → Type → Set
   Γ ⊩ A = Hil False Γ A

   _⊪_ : Ctx → Type → Set
   Γ ⊪ A = Hil True Γ A

   data Hil : Bool → Ctx → Type → Set where
      hyp : ∀{b Γ A} → A ∈ Γ → Hil b Γ A
      4□ : ∀{Γ A} → Γ ⊪ (□ A)

module AXIOMS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF


  

   infix 4 ⊩_
   ⊩_ : Type → Set
   ⊩ A = ∀{Γ w} → Γ ⊢ A [ w ]

   -- Intuitionstic modal logic
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

   ax□ : ∀{A B} → ⊩ □ (A ⊃ B) ⊃ (□ A ⊃ □ B)
   ax□ = ⊃I (⊃I (□E (hyp (S Z))
      λ DAB → □E (hyp Z) 
      λ DA → □I (λ ω → ⊃E (DAB ω) (DA ω))))
   
   axK◇ : ∀{A B} → ⊩ □ (A ⊃ B) ⊃ (◇ A ⊃ ◇ B) 
   axK◇ = ⊃I (⊃I (□E (hyp (S Z)) 
      λ DAB → ◇E (hyp Z) 
      λ ω DA → ◇I ω (⊃E (DAB ω) DA)))

{-
   ax4□ : ∀{A} → Trans →  ⊩ □ A ⊃ □ (□ A)
   ax4□ _≺≺_ = ⊃I (□E (hyp Z) λ D → □I (λ ω → □I (λ ω' → D (ω ≺≺ ω'))))

   ax4◇ : ∀{A} → Trans →  ⊩ ◇ (◇ A) ⊃ ◇ A
   ax4◇ _≺≺_ = ⊃I (◇E (hyp Z) (λ ω D → ◇I ω {!!}))
-}

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

module COUNTERMODELS where
   open import Accessibility.Nat

   infix 4 ⊮_
   ⊮_ : Type → Set₁
   ⊮ A = ∃ λ UWF → ∃ λ Γ → ∃ λ w → CORE._⊢_[_] UWF Γ A w → Void

   -- ax◇C1 : ⊩ ◇ A ⊃ ((□ (A ⊃ ⊥)) ⊃ ⊥)
   -- ax◇C2 : ⊩ ((□ (A ⊃ ⊥)) ⊃ ⊥) ⊃ ◇ A 
   -- ¬axD : ⊮ ◇ ⊤
   -- ¬axT□ : ⊮ □ A ⊃ A
   -- ¬axT◇ : ⊮ A ⊃ ◇ A
   -- ¬axB◇ : ⊮ ◇ (□ A) ⊃ A
   -- ¬axB□ : ⊮ A ⊃ □ (◇ A)
   -- ¬ax4□ : ⊮ □ A ⊃ □ (□ A) -- DONE
   -- ¬ax4◇ : ⊮ ◇ (◇ A) ⊃ ◇ A -- DONE
   -- ¬ax5□ : ⊮ ◇ (□ A) ⊃ □ A
   -- ¬ax5◇ : ⊮ ◇ A ⊃ □ (◇ A) 
   -- ¬ax2 : ⊮ ◇ (□ A) ⊃ □ (◇ A) 
   -- ¬axWJ3 : ⊮ ◇ ⊥ ⊃ ⊥
   -- ¬axSW : ⊮ (◇ A ⊃ □ B) ⊃ □ (A ⊃ B)

   Q₁ = a "q1"

   ¬ax4 : ⊮ □ Q₁ ⊃ □ (□ Q₁)
   ¬ax4 = Count , [ Q₁ at 1 ] , 2 , λ D → counter2' (nd→seq D)
    where
      open ILIST Count
      open CORE Count
      open EQUIV Count

      counter0 : □ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ Q₁ [ 0 ] → Void
      counter0 (hyp (S (S ())))
      counter0 (⊃L (S (S ())) _ _) 
      counter0 (⊥L (S (S ())))
      counter0 (◇L (S (S ())) _) 
      counter0 (□L (S (S ())) _) 
      counter0 (¬◇L (S (S ())) _)
      counter0 (¬□L (S (S ())) _)

      counter1 : □ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ □ Q₁ [ 1 ] → Void
      counter1 (□R D) = counter0 (D refl)
      counter1 (⊃L (S (S ())) _ _) 
      counter1 (⊥L (S (S ())))
      counter1 (◇L (S (S ())) _) 
      counter1 (□L (S (S ())) _) 
      counter1 (¬◇L (S (S ())) _)
      counter1 (¬□L (S (S ())) _)

      counter2 : □ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ □ (□ Q₁) [ 2 ] → Void
      counter2 (□R D) = counter1 (D refl)
      counter2 (□L Z D) = 
         counter2 
          (D (λ eq → 
           coe (resp (λ w → □ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ Q₁ [ w ]) (symm eq))
            (hyp (S Z)))) 
      counter2 (⊃L (S (S ())) _ _) 
      counter2 (⊥L (S (S ())))
      counter2 (◇L (S (S ())) _) 
      counter2 (□L (S (S ())) _) 
      counter2 (¬◇L (S (S ())) _)
      counter2 (¬□L (S (S ())) _)

      counter2' : [ Q₁ at 1 ] ⇒ □ Q₁ ⊃ □ (□ Q₁) [ 2 ] → Void
      counter2' (⊃R D) = counter2 D
      counter2' (⊃L (S ()) _ _) 
      counter2' (⊥L (S ()))
      counter2' (◇L (S ()) _) 
      counter2' (□L (S ()) _) 
      counter2' (¬◇L (S ()) _)
      counter2' (¬□L (S ()) _)

   ¬ax4◇ : ⊮ ◇ Q₁ ⊃ ◇ (◇ Q₁)
   ¬ax4◇ = Count , [ Q₁ at 1 ] , 2 , λ D → counter2' (nd→seq D) 
    where
      open ILIST Count
      open CORE Count
      open EQUIV Count

      counter2 : ◇ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ ◇ (◇ Q₁) [ 2 ] → Void
      counter2 (◇L Z D) = counter2 (D refl (hyp (S Z)))
      counter2 (◇R Refl (◇R Refl (hyp (S (S ())))))
      counter2 (◇R Refl (◇R Refl (⊃L (S (S ())) _ _)))
      counter2 (◇R Refl (◇R Refl (⊥L (S (S ())))))
      counter2 (◇R Refl (◇R Refl (◇L (S (S ())) _)))
      counter2 (◇R Refl (◇R Refl (□L (S (S ())) _)))
      counter2 (◇R Refl (◇R Refl (¬◇L (S (S ())) _)))
      counter2 (◇R Refl (◇R Refl (¬□L (S (S ())) _)))
      counter2 (◇R Refl (⊃L (S (S ())) _ _)) 
      counter2 (◇R Refl (⊥L (S (S ())))) 
      counter2 (◇R Refl (◇L (S (S ())) _))
      counter2 (◇R Refl (□L (S (S ())) _))
      counter2 (◇R Refl (¬◇L (S (S ())) _))
      counter2 (◇R Refl (¬□L (S (S ())) _))
      counter2 (⊃L (S (S ())) _ _) 
      counter2 (⊥L (S (S ())))
      counter2 (◇L (S (S ())) _) 
      counter2 (□L (S (S ())) _) 
      counter2 (¬◇L (S (S ())) _)
      counter2 (¬□L (S (S ())) _)

      counter2' : [ Q₁ at 1 ] ⇒ ◇ Q₁ ⊃ ◇ (◇ Q₁) [ 2 ] → Void
      counter2' (⊃R D) = counter2 D
      counter2' (⊃L (S ()) _ _) 
      counter2' (⊥L (S ()))
      counter2' (◇L (S ()) _) 
      counter2' (□L (S ()) _) 
      counter2' (¬◇L (S ()) _)
      counter2' (¬□L (S ()) _)



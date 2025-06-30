Require Import StringOfTerm.

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

Ltac is_definition H :=
  tryif tryif clearbody H then fail else idtac then fail else idtac.

Ltac revert_until_definition :=
  repeat lazymatch goal with
    | H : _ |- _ => tryif is_definition H then idtac else revert H
    | _ => idtac
    end.

Definition goal {A : Type} (a : A) := a.

Ltac block_goal := match goal with [ |- ?T ] => change (goal T) end.
Ltac unblock_goal := unfold goal in *.


Ltac save_context :=
  block_goal;
  revert_until_definition.

Ltac release_context :=
  intros;
  unblock_goal.

Ltac print_goal :=
  match goal with
    |- ?g => idtac "⊢ " g
  end.


(** * HELPERS  *)

Inductive Boxer : Type :=
  | box : forall {A : Type}, A -> Boxer.


Definition find_thm (l : list (string * Boxer)) (name : string) : option Boxer :=
  match List.find (fun '(n, _) => String.eqb n name) l with
  | Some (_, b) => Some b
  | None => None
  end.


Ltac make_n_evar n T :=
  do n (let x := fresh in evar (x : T)).

(* Inductive ticket : Set :=
  | Ticket : ticket.

Tactic Notation "seq_n" tactic(tac) constr(n) tactic(then_tac) :=
  make_n_evar n ticket;
  tac; (
    let k := fresh "k" in
    pose (k := O);
    repeat lazymatch goal with
    | H := ?v : ticket |- _ =>
      tryif is_evar v then (
        instantiate (H := Ticket);
        then_tac k;
        admit)
      else
        lazymatch goal with
        | _ := ?k' : nat |- _ =>
          let k'' := eval compute in (S k') in
          clear H k;
          pose (k := k'')
        end
    | _ => fail "seq_n : wrong number of subgoals"
    end).

Goal True.
  timeout 1 (seq_n ltac:(assert False) 2%nat ltac:(fun k => idtac k)). *)



(* ? convention : compare A B = true si A < B *)
Fixpoint insert_by {A} (compare : A -> A -> bool) (x : A) (l : list A) : list A :=
  match l with
  | [] => [x]
  | y :: ys => if compare x y then x :: y :: ys else y :: insert_by compare x ys
  end.

(* ! le tri n'est pas stable, problème ? *)
Fixpoint sort_by {A} (compare : A -> A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => insert_by compare x (sort_by compare xs)
  end.

Ltac print_last_string :=
  lazymatch goal with
  | _ := ?s |- _ => idtac s
  end.

Ltac print_all_definitions :=
  block_goal;
  repeat lazymatch goal with
  | H := ?v |- _ =>
    tryif is_evar v then (idtac H " evar"; generalize dependent H)
    else (idtac H " := " v; generalize dependent H)
  | _ => idtac
  end;
  intros;
  unfold goal in *.

Require Import Ascii.

(* renvoie la string prefixe bien parenthésée la plus grande *)
Fixpoint extract_block (n nb : nat) (s : string) : string :=
  match n, s with
  | S n', String _ s' => extract_block n' nb s'
  | 0, String b s' =>
    match b with
    | "("%char => String b (extract_block n (nb+1) s')
    | ")"%char =>
      match nb with
      | 0 => ""
      | S nb' => String b (extract_block n nb' s')
      end
    | _ => String b (extract_block n nb s')
    end
  | _, _ => ""
  end.

(* extrait le bloc de texte qui suit le mot "goal" dans la string *)
Definition extract_goal_in_string (s : string) :=
  match String.index 0%nat "goal" s with
  | Some i => extract_block (i+5) 0%nat s
  | None => "No goal found"
  end.
    

Ltac pose_string_of_extracted_goal name T :=
  let s := fresh "s" in
  pose_string_of_term s T;
  let s' := eval compute in (extract_goal_in_string s) in
  pose (name := s');
  clear s.

(* TODO : utiliser une approche de backtracking pour trouver les bonnes hypothèses
   à utiliser, ce qui peut permettre d'éviter de redonner la liste complète des
   hypothèse en argument pour l'assertion *)
Ltac specialize_with_ctx H :=
  repeat 
    lazymatch type of H with
    | ?T -> _ =>
      lazymatch reverse goal with
      | H' : T |- _ => specialize (H H')
      end
    | _ => idtac
    end.

(** renames all variables in the context with a fresh new name *)
Ltac rename_ctx :=
  block_goal;
  repeat lazymatch goal with
  | H := _ |- _ => revert H
  | H : ?T |- _ =>
    let ty := type of T in
    tryif unify ty Set then
      let H' := fresh H in
      rename H into H';
      revert H'
    else
      revert H
  end;
  intros;
  unfold goal at 1.

Ltac pose_compute name v :=
  let s' := eval compute in v in
  pose (name := s').

Tactic Notation "pose_compute" "(" ident(name) ":=" constr(v) ")" :=
  pose_compute name v.

Ltac instantiate_compute name v :=
  let s' := eval compute in v in
  instantiate (name := s').

Tactic Notation "instantiate_compute" "(" ident(name) ":=" constr(v) ")" :=
  instantiate_compute name v.


Ltac pose_string_of_goal name :=
  lazymatch goal with
  | |- ?g => pose_string_of_term name g
  end.


Notation "x ++ y" := (String.append x y) (at level 60, right associativity).

Ltac inst_conclusion name ccl_string verbose :=
  lazymatch verbose with
  | true =>
    let s := fresh "s" in
    pose_string_of_goal s;
    instantiate_compute name ("On conclut que " ++ s ++ ccl_string);
    clear s
  | false =>
    instantiate_compute name ("On conclut" ++ ccl_string)
  end.

Ltac merge_last_n_with_sep name n sep :=
  lazymatch n with
  | 0%nat => pose (name := "")
  | S ?n' =>
    merge_last_n_with_sep name n' sep;
    lazymatch goal with
    | H1 := ?s1 |- _ =>
      clear H1; 
      lazymatch goal with
      | H2 := ?s2 |- _ =>
        clear H2;
        pose_compute name (s2 ++ sep ++ s1)
      end
    end
  end.

Ltac merge_last_n_with_sep_rev name n sep :=
  lazymatch n with
  | 0%nat => pose (name := "")
  | S ?n' =>
    merge_last_n_with_sep name n' sep;
    lazymatch goal with
    | H1 := ?s1 |- _ =>
      clear H1; 
      lazymatch goal with
      | H2 := ?s2 |- _ =>
        clear H2;
        pose_compute name (s1 ++ sep ++ s2)
      end
    end
  end.

Ltac iter_list l tac :=
  lazymatch l with
  | [] => idtac
  | [?x] => tac x
  | ?x :: ?xs =>
    tac x;
    iter_list xs tac
  end.

Definition new_line_char := "013"%char.

Definition new_line := String new_line_char "".


(** * STRUCTURES *)


(** les théorèmes utilisés peuvent avoir un nom ou non *)
Inductive Thm : Type :=
  | named : string -> Thm
  | unnamed : forall {A : Type}, A -> Thm.



Axiom Rmult_integral_contrapositive_currified : forall x y, x <> 0 -> y <> 0 -> x * y <> 0.

(** On retrouve ici la liste des théorèmes utilisables en citant leur nom  *)
Definition thm_list : list (string * Boxer) :=
  [ ("test", box Rmult_integral_contrapositive_currified) ].


(** ? QUESTION : utile d'ajouter un flag pour classifier le cadre de
    ? l'appel d'un théorème ? (e.g prouver le but, obtenir une nouvelle hypothèse etc...)  *)

Inductive Construction : Type :=
  | trou : Construction
  (** permet d'admettre certains faits  *)
  | hypothese : Construction
  | calcul : Construction
  | introduction_variable : Construction -> Construction
  (** on stocke également la suite de la preuve  *)
  | introduction_hypothese : Construction -> Construction
  (** idem  *)
  | application : Thm -> list Thm_arg -> Construction
  (** les arguments comportent toutes les informations nécessaires pour
      finir la preuve *)
  | assertion : forall {A : Type}, A -> Construction -> Construction -> Construction
  (** FIXME : update commentaire *)

(** on fait ici la distinction entre les arguments prouvés précédemment et
    qui restent à prouver lors de l'application d'un théorème  *)
with Thm_arg : Type :=
  | forward : forall {A : Type}, A -> Thm_arg
  (** Argument prouvé avant l'application du thm. On ne stocke pas la preuve
      puisqu'elle a déjà été créée avant *)
  | backward : forall {A : Type}, A -> Construction -> Thm_arg.
  (** Argument prouvé après l'application du thm. On stocke la preuve à ce
      moment là *)

Inductive Arbre : Type :=
  | racine : 
      forall {A : Type}, A -> Construction -> Arbre.
  (** la racine de l'arbre contient le but de la preuve ainsi que la structure
      de la preuve *)


(** * CONSTRUCTION  *)

Definition is_forward (a : Thm_arg) : bool :=
  match a with
  | forward _ => true
  | backward _ _ => false
  end.

Ltac pose_string_of_forward_args name args :=
  lazymatch args with
  | [] => pose (name := "")
  | [ forward ?a ] => pose_string_of_extracted_goal name a
  | [ forward ?a; forward ?b ] =>
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    pose_string_of_extracted_goal s1 a;
    pose_string_of_extracted_goal s2 b;
    pose_compute name (s1 ++ " et " ++ s2);
    clear s1 s2
  | forward ?a :: ?rest => 
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    pose_string_of_extracted_goal s1 a;
    pose_string_of_forward_args s2 rest;
    pose_compute name (s1 ++ ", " ++ s2);
    clear s1 s2
  | _ => fail "Invalid forward arguments list"
  end.

Ltac pose_string_of_backward_args name args :=
  lazymatch args with
  | [] => pose (name := "")
  | [ backward ?a _ ] => pose_string_of_extracted_goal name a
  | [ backward ?a _; backward ?b _ ] =>
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    pose_string_of_extracted_goal s1 a;
    pose_string_of_extracted_goal s2 b;
    pose_compute name (s1 ++ " et " ++ s2);
    clear s1 s2
  | backward ?a _ :: ?rest => 
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    pose_string_of_extracted_goal s1 a;
    pose_string_of_backward_args s2 rest;
    pose_compute name (s1 ++ ", " ++ s2);
    clear s1 s2
  | _ => fail "Invalid backward arguments list"
  end.


Ltac pose_string_of_construct name a verbose :=
  lazymatch a with

  (* introduction de variable *)
  | introduction_variable ?fils =>
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    let s3 := fresh "s" in
    let H := fresh "H" in
    evar (s3 : string);
    lazymatch goal with
    | |- forall (x : ?T), _ =>
      pose_string_of_intropattern s1 x;
      pose_string_of_term s2 T;
      enough (H : name = "Soit " ++ s1 ++ " ∈ " ++ s2 ++ "\n" ++ s3);
      [> clear H; intro; pose_string_of_construct s3 fils verbose |
          unfold s1, s2, s3, name; reflexivity ]
    end

  (* introduction d'hypothèse *)
  | introduction_hypothese ?fils =>
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    let H := fresh "H" in
    evar (s2 : string);
    lazymatch goal with
    | |- ?hyp -> _ =>
      pose_string_of_term s1 hyp;
      enough (H : name = "Supposons " ++ s1 ++ "\n" ++ s2);
      [> clear H; intro; pose_string_of_construct s2 fils verbose |
         unfold s1, s2, name; reflexivity ]
    end

  (* hypothese *)
  | hypothese => 
    inst_conclusion name " par hypothèse.\n" verbose;
    assumption

  (* trou *)
  | trou =>
    let s := fresh "s" in
    pose_string_of_goal s;
    instantiate_compute name ("On admet que " ++ s ++ ".\n");
    admit

  (* assertion *)
  | assertion ?a ?fils1 ?fils2 =>
    (* étapes suivies :
        - on récupère la string correspondant à ce que l'on affirme
        - on applique la tactique assert
        + on renomme le contexte avec des variables fraiches pour qu'il n'y
          ait pas de renommage lors de l'introduction des variables
        + on introduit les variables et on unfold le goal pour retomber sur
          le vrai but que l'on cherche
        + on construit la string associée en prouvant le but avec le sous-arbre 1
        - on spécalise l'hypothèse que l'on vient de prouver pour obtenir uniquement
          la partie à l'intérieur du goal
        - enfin on finit la construction en finissant la preuve grâce au sous-arbre 2  *)
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    let s3 := fresh "s" in
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    evar (s2 : string);
    evar (s3 : string);
    pose_string_of_extracted_goal s1 a;
    enough (H1 : name = "On affirme que " ++ s1 ++ ". Montrons le.\n" ++ s2 ++ s3);
    [> clear H1; assert (H2 : a); 
        [> rename_ctx; intros; unfold goal; pose_string_of_construct s2 fils1 verbose |
           specialize_with_ctx H2; unfold goal in H2; pose_string_of_construct s3 fils2 verbose ] |
      unfold s1, s2, s3, name; reflexivity ]

  (* application *)
  | application (named ?thm_name) ?args =>
    let thm_ty := constr:(find_thm thm_list thm_name) in
    lazymatch eval compute in thm_ty with
    | Some (box ?thm) =>
      let args := constr:(List.partition is_forward args) in
      let args := eval simpl in args in
      let H := fresh "H" in
      lazymatch args with
      | ([], []) =>
        let s := fresh "s" in
        pose_string_of_goal s;
        instantiate_compute name ("Par " ++ thm_name ++ ", on conclut que " ++ s ++ ".\n");
        apply thm
      | (?f, []) =>
        let s := fresh "s" in
        let s2 := fresh "s" in
        pose_string_of_goal s;
        pose_string_of_forward_args s2 f;
        instantiate_compute name ("Par " ++ thm_name ++ " en utilisant que " ++ s2 ++ ", on conclut que " ++ s ++ ".\n");
        apply thm; assumption
        (* ? assumption est-elle vraiment la tactique qu'on veut utiliser ? *)
      | ([], ?b) =>
        let s := fresh "s" in
        pose_string_of_backward_args s b;
        let s2 := fresh "s" in
        merge_proofs_of_backward_args s2 b;
        instantiate_compute name ("Par " ++ thm_name ++ ", il suffit de montrer que " ++ s ++ ".\n" ++ s2);
        apply thm; assumption
      | (?f, ?b) =>
        let s1 := fresh "s" in
        let s2 := fresh "s" in
        let s3 := fresh "s" in
        pose_string_of_forward_args s1 f;
        pose_string_of_backward_args s2 b;
        merge_proofs_of_backward_args s3 b;
        instantiate_compute name ("Par " ++ thm_name ++ " en utilisant que " ++ s1 ++ ", il suffit de montrer que " ++ s2 ++ ".\n" ++ s3);
        apply thm; assumption
      end
    | None => fail "Theorem not found in the list"
    end
  |  _  =>
    instantiate (name := "TODO");
    admit
  end

with pose_proof_of_backward_args args verbose :=
  lazymatch args with
  | [] => idtac
  | [ backward ?a ?fils ] =>
    let s := fresh "s" in
    let s2 := fresh "s" in
    let s3 := fresh "s" in
    let H := fresh "H" in
    pose_string_of_extracted_goal s2 a;
    pose_compute s3 ("Montrons que " ++ s2 ++ ".\n");
    clear s2;
    evar (s : string);
    assert (H : a);
    [> rename_ctx; intros; unfold goal; pose_string_of_construct s fils verbose |
      specialize_with_ctx H; unfold goal in H ]
  | backward ?a ?fils :: ?rest =>
    let s := fresh "s" in
    let s2 := fresh "s" in
    let s3 := fresh "s" in
    let H := fresh "H" in
    pose_string_of_extracted_goal s2 a;
    pose_compute s3 ("Montrons que " ++ s2 ++ ".\n");
    clear s2;
    evar (s : string);
    assert (H : a);
    [> rename_ctx; intros; unfold goal; pose_string_of_construct s fils verbose |
      specialize_with_ctx H; unfold goal in H; pose_proof_of_backward_args rest verbose ]
  end

with merge_proofs_of_backward_args name args :=
  let n := constr:((2 * List.length args)%nat) in
  let n := eval compute in n in
  evar (name : string); (* nécessaire pour "réserver" le nom *)
  pose_proof_of_backward_args args false;
  let s := fresh "s" in
  (* FIXME : vérifier l'ordre des arguments *)
  merge_last_n_with_sep s n "";
  instantiate_compute name s;
  clear s.

Ltac inst_string_of_arbre name a verbose :=
  lazymatch a with
  | racine ?g ?c =>
    let H := fresh "H" in
    let s := fresh "s" in
    evar (s : string);
    assert (H : g); [> pose_string_of_construct s c verbose | clear H];
    lazymatch goal with
    | H := ?def |- _ =>
      clear H;
      instantiate_compute name def
    end
  end.

Ltac deduce_from_arbre a :=
  lazymatch a with
  | racine _ ?c =>
    let s := fresh "s" in
    evar (s : string);
    (* ! pas la manière la plus élégante de faire... *)
    pose_string_of_construct s c false
  end.


(** * TESTS *)

Ltac app T :=
  let ty := type of T in
  match ty with
  | Prop =>
    (* si on a affaire à une proposition, on la cherche dans le contexte *)
    match goal with
    | H : T |- _ => apply H
    | _ => fail "Cannot apply" T
    end
  | _ => 
    (* sinon, c'est un théorème et on l'applique directement *)
    apply T
  end.


Goal forall x z, x <> 0 -> z <> 0 -> x > 0.
Proof.
  intros x z.
  pose (y := 2).
  pose (y2 := 3).
  intro Hx.
  assert (forall x, x <> 0 -> goal (x <> 0)).
  rename_ctx.
  intros.
  unfold goal.
  assumption.
  specialize_with_ctx H.
  unfold goal in H.
  rename_ctx.
Abort.


Goal True.
Proof.
  evar (s : string).
  let a := constr:(racine (forall x, x <> 0 -> x * x <> 0) (
    introduction_variable
      ( introduction_hypothese
        ( application
          (named "test")
          [ forward (forall x, x <> 0 -> goal (x <> 0));
            forward (forall x, x <> 0 -> goal (x <> 0))
          ]
         )
      )
  )) in
  inst_string_of_arbre s a true.
  print_last_string.
Abort.

Goal True.
Proof.
  evar (s : string).
  let a := constr:(racine (forall x, x <> 0 -> x * x <> 0) (
    introduction_variable
      ( introduction_hypothese
        ( application
          (named "test")
          [ forward (forall x, x <> 0 -> goal (x <> 0));
            backward (forall x, x <> 0 -> goal (x <> 0)) hypothese
          ]
         )
      )
  )) in
  inst_string_of_arbre s a true.
  print_last_string.
Abort.

Goal True.
Proof.
  evar (s : string).
  let a := constr:(racine (forall x, x <> 0 -> x * x <> 0) (
    introduction_variable
      ( introduction_hypothese
        ( application
          (named "test")
          [ backward (forall x, x <> 0 -> goal (x <> 0)) trou;
            backward (forall x, x <> 0 -> goal (x <> 0)) hypothese
          ]
         )
      )
  )) in
  inst_string_of_arbre s a true.
  print_last_string.
Abort.

Goal True.
Proof.
  evar (s : string).
  let a := constr:(racine (forall x, x <> 0 -> x < 0) (
    introduction_variable (
      introduction_hypothese (
        ( assertion
          (forall x, x <> 0 -> goal (x <> 0))
          ( hypothese )
          ( trou )
        )
  )))) in
  inst_string_of_arbre s a true.
  print_last_string.
Abort.

Goal forall x, x <> 0 -> x * x <> 0.
Proof.
  let a := constr:(racine (forall x, x <> 0 -> x * x <> 0) (
    introduction_variable
      ( introduction_hypothese
        ( application
          (named "test")
          [ forward (forall x, x <> 0 -> goal (x <> 0));
            forward (forall x, x <> 0 -> goal (x <> 0))
          ]
         )
      )
  )) in
  deduce_from_arbre a.
Admitted.
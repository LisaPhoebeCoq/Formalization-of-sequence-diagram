Require Export String Bool ListSet List Arith Compare_dec Omega Ascii.
Require Import Zwf.
Require Import Coq.Program.Equality.

Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.

(*--Abstract syntax definition of sequence diagram --*)
Inductive Kind:Set:=
|Send:Kind
|Receive:Kind.

Notation "!":=Send (at level 40).
Notation "?":=Receive (at level 40).
Definition Signal:=nat.
Definition Lifeline:=nat.
Definition Message:=Signal*Lifeline*Lifeline.
Definition Event:=Kind*Message.
Definition Trace:=list Event.
Definition Model:=set Trace.


Inductive SeqDiag:Set :=
|Skip :SeqDiag
|E: Event ->SeqDiag
|Alt:SeqDiag->SeqDiag->SeqDiag
|Opt:SeqDiag->SeqDiag
|Strict:SeqDiag->SeqDiag->SeqDiag
|Loop:nat->SeqDiag->SeqDiag
|Par:SeqDiag->SeqDiag->SeqDiag.

(*--End of abstract syntax definition--*)

(*--Decision theorem--*)
Inductive id : Type := 
  Id : nat -> id.

Definition Signal_dec : forall (k1 k2:Signal), {k1 = k2} + {k1 <> k2}.
    exact eq_nat_dec.
Defined.
Definition Lifeline_dec : forall (k1 k2:Lifeline), {k1 = k2} + {k1 <> k2}.
    repeat decide equality.
Defined.

Definition Kind_dec : forall (k1 k2:Kind), {k1 = k2} + {k1 <> k2}.
   repeat decide equality. 
Defined.

Definition Event_dec:forall a b:Event,  {a = b} + {a <> b}.
Proof.
   repeat decide equality. 
Defined.

Definition Message_dec : forall (k1 k2:Message), {k1 = k2} + {k1 <> k2}.
Proof.
   repeat decide equality. 
Defined.

Theorem Trace_dec:forall a b:Trace,  {a = b} + {a <> b}.
Proof.
   repeat decide equality.
Defined.

Theorem EventPaireq_dec:forall a b:Event*Event,  {a = b} + {a <> b}.
Proof.
 repeat decide equality.
Defined.

Fixpoint beq_kind (k1 k2:Kind):bool:=
match k1 with
|!=> match k2 with
    |! =>true
    |? =>false
   end
|? => match k2 with
    |! =>false
    |? =>true
    end
end.

Fixpoint beq_event (e1:Event)(e2:Event):bool:=
match e1,e2 with
(k1,(s1,tr1,re1)),(k2,(s2,tr2,re2)) =>
    if (andb (andb (beq_kind k1 k2) (beq_nat s1 s2)) (andb (beq_nat tr1 tr2) (beq_nat re1 re2)) ) 
         then true 
         else false
end.


Fixpoint beq_trace (t1:Trace)(t2:Trace):bool:=
match t1,t2 with
|nil,nil=>true
|t1::tail1,t2::tail2=> if (beq_event t1 t2) then (beq_trace tail1 tail2) else false
|_,_ =>false
end.


Definition beq_lifeline (l1:Lifeline)(l2:Lifeline):bool:=
   beq_nat l1 l2.
(*--end of decision theorem--*)


(*--test case--*)
Definition aEvent:=(?,(1001,100,1)).
Definition bEventOut:=(!,(1002,1,2)).
Definition bEventIn:=(?,(1002,1,2)).
Definition cEventOut:=(!,(1003,1,2)).
Definition cEventIn:=(?,(1003,1,2)).
Definition e1Event:=(?,(1001,100,1)).
Definition e2Event:=(?,(1002,100,1)).
Definition e3Event:=(!,(1003,1,200)).
Definition e4Event:=(!,(1004,1,200)).
Eval compute in set_mem Message_dec (1001,100,1) ((1001,100,1)::nil).
Eval compute in set_mem Kind_dec Send (Send::nil).
Close Scope string_scope.
(*--end of test case--*)

(*--Denotation semantic of sequence diagram--*)

(*-semantic of operator strict-*)
Fixpoint OneToSet(t:Trace)(s:set Trace){struct s}:set Trace:=
match s with
|nil=>nil
|l::tail=>((t++l)::nil)++OneToSet t tail
end.

Fixpoint SetToOne(s:set Trace)(t:Trace){struct s}:set Trace:=
match s with
|nil=>nil
|l::tail=>((l++t)::nil)++SetToOne tail t
end.

Fixpoint UnionTrace(s1:set Trace)(s2:set Trace){struct s1}:set Trace:=
match s1,s2 with
|nil,_=>nil
|_,nil=>nil
|t1::tail1,t2::tail2=>((t1++t2)::nil) ++ 
                      (OneToSet t1 tail2) ++
                      (SetToOne tail1 t2) ++
                      (UnionTrace tail1 tail2)
end.


Fixpoint  unionModel(lA:set Trace)(lB:set Trace): set Trace:=
 match lA with nil => nil
 | a:: lA' => set_union Trace_dec (map (app a) lB) ( unionModel lA' lB)
 end.

Functional Scheme unionModel_ind:=
   Induction for unionModel Sort Prop.


(*test case for UnionTrace*)
Definition s1:= (aEvent::nil)::(bEventOut::nil)::nil.
Definition s2:= (aEvent::nil)::(bEventOut::nil)::nil.
Eval compute in UnionTrace s1 s2.

Definition s3:= (aEvent::nil)::(bEventOut::nil)::(cEventOut::nil)::nil.
Definition s4:= (aEvent::nil)::(bEventOut::nil)::(cEventOut::nil)::nil.
Eval compute in UnionTrace s3 s4.

(*-end of strict semantic-*)

(*-semantic of operator loop-*)
Fixpoint LoopStrictAux (s: set Trace) (s2: set Trace): (set Trace) :=
match s with
|nil => nil
|t::tail =>set_union Trace_dec ( map (app t) s2) (LoopStrictAux tail s2)
end.

Fixpoint LoopStrict (n:nat)(s: set Trace) : (set Trace) :=
match n with
|0 =>  (nil::nil)
|S n => LoopStrictAux s (LoopStrict n s )
end.

Functional Scheme LoopStrictAux_ind:=
   Induction for LoopStrictAux Sort Prop.
Functional Scheme LoopStrict_ind:=
   Induction for LoopStrict Sort Prop.
(*-end of loop semantic-*)

(*-start of par semantic-*)

Fixpoint projLifelineEve (l:Lifeline) (se: set Event) : set Event :=
match se with
|nil =>nil
|e::etail => match e with
           |(!,m) => match m with (_,tr,re) =>
                           if (beq_lifeline tr l) 
                              then e::(projLifelineEve l etail) 
                              else (projLifelineEve l etail)
                     end
           |(?,m) =>  match m with (_,tr,re) =>
                          if (beq_lifeline re l) 
                              then e::(projLifelineEve l etail) 
                              else (projLifelineEve l etail)
            end
           end
end.

Fixpoint map_prefixo (e:Event) (O:Model) :Model :=
match O with
| nil => nil
| t::R => (e::t) :: (map_prefixo e R)
end.

Fixpoint interleaveTrace (t1:Trace):Trace -> (set Trace) :=
match t1 with
| nil  => fun t2 =>(t2::nil)
| x::u => fix aux (t2:Trace) {struct t2} : set Trace:=
           match t2 with
           | nil => (t1::nil)
           | y::v => set_union Trace_dec
                (map_prefixo x (interleaveTrace u t2))
                (map_prefixo y (aux v))
           end
end.

Fixpoint interleaveModelAux (t1 :Trace)(s2:set Trace):set Trace:=
match s2 with
|nil=>nil
|t2::tail2=>set_union Trace_dec (interleaveTrace t1 t2) (interleaveModelAux t1 tail2)
end.
Functional Scheme interleaveModelAux_ind:=
   Induction for interleaveModelAux Sort Prop.


Fixpoint interleaveModel(s1:set Trace)(s2:set Trace){struct s1}:set Trace:=
match s1 with
|nil=>nil
|t1::tail1=>set_union Trace_dec (interleaveModelAux  t1 s2) (interleaveModel tail1 s2)
end.
Functional Scheme interleaveModel_ind:=
   Induction for interleaveModel Sort Prop.


(*-End of Par semantic-*)

(*--Denotation funtion--*)
Fixpoint interp (D:SeqDiag) {struct D}: Model  :=
match D with
|Skip =>((nil))::nil
|E e => (e::nil)::nil
|Strict SD1 SD2 => unionModel (interp SD1) (interp SD2)
|Alt SD1 SD2 => set_union Trace_dec (interp SD1) (interp SD2) 
|Opt SD =>set_union Trace_dec ((nil)::nil) (interp SD)
|Loop n SD => LoopStrict n (interp SD)
|Par SD1 SD2 => interleaveModel (interp SD1) (interp SD2)
end.

Functional Scheme interp_ind:=
    Induction for interp Sort Prop.

(*--end of denotation funtion--*)
(*--end of denotation semantic of sequence diagram--*)

(*--Definition of operational semantic--*)
(*-Big-step semantic-*)
Inductive execute_b:Trace ->SeqDiag->Trace  ->Prop :=
|B_SkipExec: forall t,execute_b t Skip t
|B_EventExec: forall t e ,
             execute_b t (E e) (t++(e::nil)) 
|B_StrictExec: forall  d1  d2 t  t' t'' t''',
             execute_b nil d1 t -> 
             execute_b nil d2 t'-> 
             t'' = t++t' ->
             execute_b t''' (Strict d1 d2) (t'''++t'')
|B_AltExec1: forall  d1  d2 t t'',
             execute_b nil d1 t->             
             execute_b t'' (Alt d1 d2) (t''++t)
|B_AltExec2: forall  d1  d2 t t'',
             execute_b nil d2 t->             
             execute_b t'' (Alt d1 d2) (t''++t)
|B_OptExec1:forall  d t t'',
             execute_b nil d t->
             execute_b t'' (Opt d) (t''++t)
|B_OptExec2:forall  d t,
             execute_b t (Opt d) t
|B_LoopExec: forall n d t t' t'', 
             execute_b nil d t -> execute_b nil (Loop n d) t''->execute_b t' (Loop (S n) d) (t'++t++t'')
|B_LoopSkip: forall d t, execute_b t (Loop 0 d) t
|B_ParExec: forall  d1  d2 t  t' t'' t''',
             execute_b nil d1 t -> 
             execute_b nil d2 t'-> 
             set_In t'' (interleaveTrace t t') ->
             execute_b t''' (Par d1 d2) (t'''++t'').

(*-Small-step semantic*)
Inductive red: SeqDiag*Trace ->SeqDiag*Trace  ->Prop :=
|S_SkipExec: forall t,red(Skip,t) (Skip,t)
|S_EventExec: forall e t, red(E e,t) (Skip,t ++ (e::nil))
|S_OptExec1: forall d t,red(Opt d,t) (d,t)
|S_OptExec2: forall d t, red(Opt d,t) (Skip,t)
|S_AltExec1: forall d1 d2 t,red(Alt d1 d2,t) (d1,t) 
|S_AltExec2: forall d1 d2 t,red(Alt d1 d2,t) (d2,t) 
|S_StrictExec: forall d1 d1' d2 t t' ,red(d1,t) (d1',t')-> red(Strict d1 d2,t) (Strict d1' d2,t') 
|S_StrictSKIP: forall d t', red(Strict Skip d,t') (d,t') 
|S_LoopBody:forall n d t,red (Loop (S n) d,t)(Strict d (Loop n d),t)
|S_LoopSkip:forall d t,red (Loop 0 d,t)(Skip,t)
|S_ParExec1: forall d1 d1' d2 t t' ,red(d1,t) (d1',t')-> red(Par d1 d2,t) (Par d1' d2,t') 
|S_ParExec2: forall d1 d2 d2' t t' ,red(d2,t) (d2',t')-> red(Par d1 d2,t) (Par d1 d2',t') 
|S_ParSkip1: forall d t, red(Par Skip d,t) (d,t)
|S_ParSkip2: forall d t, red(Par d Skip,t) (d,t).


Require Import Sequences.
(** The three possible outcomes of execution. *)
Definition terminates (d: SeqDiag) (t t': Trace) : Prop :=
  star red (d, t) (Skip, t').

Definition diverges (d: SeqDiag) (t: Trace) : Prop :=
  infseq red (d, t).

Definition goes_wrong (d d': SeqDiag) (t t': Trace) : Prop :=
  exists d', exists t',
  star red (d, t) (d', t') /\ d' <> Skip /\ irred red (d', t').

(*--end of definition of operational semantic--*)



(*--The proof of properties of sequence digram--*)
(*-Theorem 1: Denotation model not empty-*)

(*-Auxilary lemma of theorem 1 -*)
Lemma setunion_nil: forall l1 l2,set_union Trace_dec l1 l2 = nil-> l1=nil /\l2=nil.
Proof.
 intros l1 l2 H.
 induction l1;destruct l2;simpl in *.
 split;auto.
 split. auto. 
 contradict H. apply set_add_not_empty.
 inversion H.
 contradict H. apply set_add_not_empty.
Qed.


  Lemma LoopStrictAux_nil:forall m1 m2 ,LoopStrictAux m1 m2 = nil -> m1 = nil \/ m2 = nil.
  Proof.
   induction m1; intros; inversion H. auto. apply setunion_nil in H1. destruct H1. 
   induction m2. 
   right. rewrite H1.  simpl. auto.
   inversion H0.
Qed.


  Lemma LoopStrict_nil:forall n m, LoopStrict n m = nil -> m=nil .
  Proof.
    induction n; intros; inversion H.
  rewrite H1.
  apply  LoopStrictAux_nil in H1. destruct H1. subst. simpl. auto.
  apply IHn in H0.  assumption. 
Qed.

  Lemma map_prefixo_nil: forall e t,map_prefixo e t = nil -> t = nil.
  Proof.
    induction t; intros.
    auto.
    simpl in H. inversion H.
  Qed.

  Lemma Par_nil:forall t1 t2,interleaveTrace t1 t2 = nil ->False.
  Proof.
   induction t1; destruct t2; intros; inversion H.
   apply setunion_nil in H1. destruct H1.
   apply map_prefixo_nil in H1. 
   clear - IHt1 H0.
   apply map_prefixo_nil in H0.
   apply IHt1 in H0. inversion H0.
 Qed.
(*-end of auxilary lemma -*)

Lemma interpnil_false: forall d,interp d = nil -> False.
Proof.
  induction d. 

  (*SKIP*)
  intros H. inversion H.

  (*EVENT*)
  intros H. inversion H.

  (*ALT*)
  intros H. inversion H.
  apply setunion_nil in H1.
  destruct H1. apply IHd1 in H0. inversion H0.

  (*OPT*)
  intros H. inversion H.
  apply setunion_nil in H1.
  destruct H1. apply IHd in H1. inversion H0.
 
  (*STRICT*)
  intros H. inversion H.
  induction (interp d1); destruct (interp d2).
    simpl in H1. apply IHd1 in H1. inversion H1.
    simpl in H1. apply IHd1 in H1. inversion H1.
    simpl in H1. apply IHd2. auto. 
    simpl in H1. apply IHm. apply setunion_nil in H1. destruct H1. inversion H0.
    apply setunion_nil in H1. destruct H1.  assumption.

  (*LOOP*)
  induction n. intros. inversion H.
  intros. inversion H. remember (interp d) as m.
  induction m. apply IHd.  auto. 
  simpl in H1. SearchAbout set_union. apply setunion_nil in H1. destruct H1.
  apply map_eq_nil in H0.
  apply  LoopStrict_nil in H0. inversion H0.

  (*PAR*)
   intros H. inversion H.
   induction (interp d1); destruct (interp d2).
    simpl in H1. apply IHd1 in H1. inversion H1.
    simpl in H1. apply IHd1 in H1. inversion H1.
    simpl in H1. apply IHd2. auto. 
    simpl in H1.  apply setunion_nil in H1. destruct H1.
    apply setunion_nil in H0. destruct H0. clear IHd1 IHd2.
    apply Par_nil in H0. inversion H0.
Qed.
(*-end of theorem 1-*)


(*-Auxilary lemma of theorem 2 -*)
    Lemma setIn_map:forall e t m, set_In t m <-> set_In (e::t) (map_prefixo e m).
    Proof.
     induction m;split;intros.
     inversion H.
     inversion H.
     simpl in H. destruct H.
     subst. simpl. auto.
     apply IHm in H. simpl. right. assumption.
     simpl in H. destruct H. inversion H. simpl. auto.
     apply IHm in H. simpl. right. auto.
    Qed.

  Lemma strict_in_inter:forall x x0,set_In (x ++ x0) (interleaveTrace x x0).
  Proof.
    induction x; intros.
    simpl. auto.
    simpl. remember (IHx x0) as H. clear HeqH.
    clear IHx. induction x0. 
    simpl.  left. rewrite app_nil_r. auto.
    apply set_union_intro. left.
    apply setIn_map. assumption.
  Qed.
(*-end of auxilary lemma -*)

(*-Theorem 2: Termination-*)
Theorem Termination :forall d:SeqDiag, (exists t,execute_b nil d t).
Proof.
  intros d. 
  induction d.
  exists nil. constructor.
  exists (e::nil). constructor.
  destruct IHd1. destruct IHd2. exists x. apply B_AltExec1 with (t:=x). assumption.
  destruct IHd. exists nil. apply B_OptExec2.
  destruct IHd1. destruct IHd2. 
  exists (x++x0). apply B_StrictExec with (t:=x)(t':=x0)(t''':=nil). assumption. assumption. auto.
  destruct IHd. induction n. exists nil. constructor.
  destruct IHn.  exists (nil++x++x0). apply B_LoopExec.  assumption. assumption.
  destruct IHd1. destruct IHd2.   
  exists (nil++(x++x0)).  apply B_ParExec with(t:=x)(t':=x0);try assumption.
  apply strict_in_inter. 
Qed. 
(*-end of theorem 2-*)

(*--Equvilance of Big-step semantic and small-step semantic--*)
(*-Proof of theorem 3-*)
(*-Auxilary lemma of theorem 3 -*)
Remark star_red_seq_left:
  forall d t d' t' d2,
  star red (d, t) (d', t') ->
  star red (Strict d d2, t) (Strict d' d2, t').
Proof.
dependent induction H. constructor.
  destruct b. econstructor. constructor; eauto. eauto. 
Qed. 


Lemma exec_inittrace:forall d d' t0 t t',red(d,t0)(d',t') <-> red(d,t++t0)(d',t++t') .
Proof.
   induction d;split;intros.
   (*SKIP*)
   inversion H;subst. simpl.
   constructor.
  
   inversion H;subst. apply app_inv_head in H3. rewrite H3.
   constructor.

   (*EVENT*)
   inversion H;subst. simpl.
   remember (t++t0) as t'. rewrite app_assoc. rewrite <- Heqt'.
   constructor.

   inversion H;subst. simpl.
   rewrite <- app_assoc in H4. apply app_inv_head in H4. rewrite <- H4.
   constructor.
   
   (*ALT*)
   inversion H;subst. simpl.
   constructor.
   constructor.

   inversion H;subst; apply app_inv_head in H5; subst. 
   constructor. constructor.

   (*OPT*) 
    inversion H;subst. simpl.
    constructor.
    constructor.

   inversion H;subst;apply app_inv_head in H4; subst;constructor. 
    
   (*STRICT*)
    inversion H;subst. simpl.
    constructor. now apply IHd1.
    constructor.

    inversion H;subst. apply IHd1 in H1. now constructor.
    apply app_inv_head in H5. subst. constructor.
  
   (*LOOP*)
   intros. inversion H; subst.
   constructor.
   constructor.

   inversion H;subst;apply app_inv_head in H5; subst; constructor.

   (*PAR*)
   intros. inversion H;subst.
   constructor. now apply IHd1.
   constructor. now apply IHd2.
   constructor. constructor.

   inversion H;subst.
   apply IHd1 in H1. now constructor.
   apply IHd2 in H1. now constructor.
   apply app_inv_head in H5; subst; constructor.
   apply app_inv_head in H5; subst; constructor.
Qed.


Lemma execcute_s_init:forall d d' t t',red (d, t) (d', t') -> exists t'',t' = t++t''.
Proof.
 induction d;intros;inversion H;subst.
  (*SKIP*)
  exists nil. rewrite app_nil_r. auto.
  (*EVENT*)
  exists (e::nil).  auto.
  (*ALT1*)
  exists nil. rewrite app_nil_r. auto.
  (*ALT2*)
  exists nil. rewrite app_nil_r. auto.
  (*OPT*)
  exists nil. rewrite app_nil_r. auto.
  (*OPTSKIP*)
  exists nil. rewrite app_nil_r. auto.
  (*STRICT1*)
  apply IHd1 in H1. destruct H1.
  exists x. auto.
  (*STRICT2*)
  exists nil. rewrite app_nil_r. auto.
  (*LOOPN*)
  exists nil. rewrite app_nil_r. auto.
  (*LOOP0*)
  exists nil. rewrite app_nil_r. auto.
  (*PAR1*)
  apply IHd1 in H1.  destruct H1.  subst.  exists x. auto.
  (*PAR2*)
  apply IHd2 in H1.  destruct H1.  subst.  exists x. auto.
  (*PAR3*)
  exists nil. rewrite app_nil_r. auto.
  (*PAR4*)
  exists nil. rewrite app_nil_r. auto.
Qed.

Lemma exec_star_inittrace:forall d d' t0  t t',star red(d,t0)(d',t')  <-> star red(d,t++t0)(d',t++t') .
Proof.
   split.
   intros. dependent induction  H. 
      apply star_refl.
      destruct b. apply star_step with (s, t++ t1). apply exec_inittrace. assumption.
      now apply IHstar.
   intros.  dependent induction  H. 
      apply app_inv_head in x. subst. apply star_refl.
      destruct b.
      remember H as H10. clear HeqH10.
      apply execcute_s_init in H. destruct H. subst.
      apply star_step with (s, t0++x). rewrite <- app_assoc in H10. rewrite <- exec_inittrace in H10. assumption.
      rewrite <- app_assoc in IHstar.
      apply IHstar with(t2:=t)(t1:=t0++x).
      auto. auto. 
Qed.


Lemma execute_b_plus :forall d t t',execute_b t d (t++t') -> execute_b nil d t'.
Proof.
  induction d. 
  (*SKIP*) 
   intros. inversion H. apply eq_sym in H2. rewrite <- app_nil_r in H2.  SearchAbout app.
   apply app_inv_head in H2. subst. constructor.

  (*EVENT*)
   intros. inversion H;subst. apply app_inv_head in H3. subst. constructor.
   
  (*ALT*)
   intros. inversion H;subst. apply app_inv_head in H4. subst. rewrite <- app_nil_l. constructor. assumption.
   apply app_inv_head in H4. subst. rewrite <- app_nil_l. apply B_AltExec2. assumption.
   

  (*OPT*)
   intros. inversion H.  apply app_inv_head in H2. subst. rewrite <- app_nil_l. constructor. assumption.
   apply eq_sym in H1. rewrite <- app_nil_r in H1. apply app_inv_head in H1. subst. constructor.

  (*STRICT*)
  intros. inversion H. subst. apply app_inv_head in H2. subst. rewrite <- app_nil_l. now apply B_StrictExec with (t:=t0)(t':=t'0).

  (*LOOP*)
  intros. inversion H. subst. apply app_inv_head in H3. subst. rewrite <- app_nil_l.  constructor. assumption. assumption.
  apply eq_sym in H1. rewrite <- app_nil_r in H1. apply app_inv_head in H1. subst. constructor.

  (*PAR*)
  intros. inversion H. subst. apply app_inv_head in H2. subst.
   rewrite <- app_nil_l.  apply B_ParExec with (t:=t0)(t':=t'0);assumption.
Qed.

Lemma execute_b_plus_re :forall d t t',  execute_b nil d t' -> execute_b t d (t++t').
Proof.
   induction d;intros;inversion H. subst.
  
   (*SKIP*)
   rewrite app_nil_r. constructor.

   (*EVENT*)
   simpl in H1. subst. simpl. constructor.

   (*ALT*)
    simpl in H2. subst. simpl. constructor. auto.
    simpl in H2. subst. simpl. apply B_AltExec2. auto.

   (*OPT*)
    simpl in H2. subst. simpl. constructor. auto.
    simpl in H2. subst. simpl. rewrite app_nil_r. apply B_OptExec2.
  
   (*STRICT*)
    simpl in H5. subst. rewrite <- H5. apply B_StrictExec with (t:=t0)(t':=t'0). assumption. assumption. auto.

   (*LOOP*)
   simpl in H4. subst. simpl. constructor.  auto. auto.
   subst. rewrite app_nil_r. apply B_LoopSkip.

   (*PAR*)
   simpl in H5. subst. apply B_ParExec with (t:=t0)(t':=t'0). assumption. assumption. auto.
Qed.

Lemma app_equal_nil:forall (t t':Trace), t = t ++t'-> t'= nil.
Proof.
  induction t;intros.
  simpl in H. subst. auto.
  simpl in H. inversion H.  now apply IHt. 
Qed.

Lemma star_Skip_nil: forall t0 t1 t2,star red (Skip, t0++t1) (Skip, t0 ++ t2) -> t1 = t2.
Proof.
 intros.
 dependent induction H.
 apply app_inv_head in x. assumption.
 inversion H;subst.
 now apply IHstar with (t3:=t0). 
Qed.

Lemma star_Skip_False:forall t0 t', star red (Skip, t0) (Skip, t0 ++ t') -> t'<>nil -> False.
Proof.
 intros.
 dependent induction H.
 apply app_equal_nil in x.  intuition.
 destruct b. inversion H. subst.
 now apply IHstar with(t0:=t)(t'0:=t'). 
Qed.
 
Lemma map_prefixo_aux:forall e e' t t',set_In (e::t) (map_prefixo e' t')-> e = e'.
Proof.
 induction t';intros. 
 simpl in H. inversion H.
 simpl in H. destruct H.
 inversion H. auto.
 now apply IHt'.
Qed.


Lemma interleaveTrace_nil:forall t,interleaveTrace t nil = t::nil.
Proof.
 destruct t. simpl. auto. simpl. auto.
Qed.

Lemma interleaveTrace_app_rev:forall e t'' t t',set_In (e::t'') (interleaveTrace t t')
                 -> exists t3,(t = e::t3 /\ set_In (e :: t'') (map_prefixo e (interleaveTrace t3 t')))
                            \/(t' = e::t3/\ set_In (e :: t'') (map_prefixo e (interleaveTrace t t3))).
Proof.
 induction t;intros.
 simpl in H. destruct H.
 exists t''. right. split. auto. simpl. auto.
 inversion H.
 induction t'.
 simpl in H. inversion H. 
 exists t''. left. split. auto. apply setIn_map. rewrite interleaveTrace_nil. 
 simpl. auto.
 inversion H0. 
 simpl in H. 
 apply set_union_elim in H. 
 destruct H.  remember H as H10. clear HeqH10. 
 apply map_prefixo_aux in H. subst.
 exists t. left. split. auto. auto. 
  remember H as H10. clear HeqH10. 
 apply map_prefixo_aux in H. subst.
 exists t'. right. split. auto. assumption.
Qed.



Lemma star_exec_s:forall d d' t t',star red (d, t) (d', t') ->exists t'', t' = t ++ t''.
Proof.
  intros. dependent induction H.  
  exists nil. rewrite app_nil_r. auto.
  destruct b. apply execcute_s_init in H. destruct H. subst.
  assert ((s, t ++ x) = (s,t++x)). auto. apply IHstar with (t'0:=t')(d'0 := d') in H .
  destruct H. rewrite <- app_assoc in H. exists (x++x0). assumption. auto.
Qed.
 
Lemma  star_exec_par:forall d1 d2 t t0,star red (d1, t0) (Skip, t0 ++ t) -> star red (Par d1 d2, t0) (Par Skip d2, t0 ++ t).
Proof.
 intros. dependent induction H. apply app_equal_nil in x. subst.
 rewrite app_nil_r. apply star_refl.
 destruct b.
 remember H as H2. clear HeqH2.
 apply execcute_s_init in H2. apply star_step with (Par s d2, t1). now constructor.
 destruct H2.
 apply star_exec_s in H0. destruct H0. rewrite H1 in H0. rewrite <- app_assoc in H0.
 apply app_inv_head in H0. rewrite H0. rewrite app_assoc. rewrite <- H1.
 apply IHstar. auto. rewrite H1. rewrite <- app_assoc. rewrite H0. auto.
Qed.

Lemma interleaveTrace_aux:forall e t1 t2 t,set_In (e::t) (interleaveTrace (e::t1) t2) 
                                    ->set_In (e :: t) (map_prefixo e (interleaveTrace t1 t2))                 
                                    ->set_In t (interleaveTrace t1 t2).
Proof.
  
   intros.
   destruct t2.  simpl in H. 
   inversion H. rewrite interleaveTrace_nil. inversion H1. subst.
   simpl. auto.
   inversion H1.
   simpl.  apply setIn_map in H0.  assumption.
Qed.

Lemma interleaveTrace_aux_r:forall e t1 t2 t,set_In (e::t) (interleaveTrace t1 (e::t2)) 
                                    ->set_In (e :: t) (map_prefixo e (interleaveTrace t1 t2))                     
                                    ->set_In t (interleaveTrace t1 t2).
Proof.
 intros.  apply setIn_map in H0. assumption.  
Qed.
  

Lemma star_aux_strict:forall d1 d2 t0 t, star red (Strict d1 d2, t0) (Skip, t0 ++ t)
                            -> exists t', star red (d1,t0) (Skip,t0++t') 
                             /\ exists t'',star red (d2,t0) (Skip,t0++t'') /\ t = t'++t''.
Proof.
 intros.
 dependent induction H.
 inversion H;subst.
 remember H0 as H1. clear HeqH1.
 apply star_exec_s in H1.  destruct H1.
 assert ((Strict d1' d2, t') = (Strict d1' d2, t')).
 auto.
 apply IHstar with (t2:=x) in H2.
 destruct H2. destruct H2. destruct H3. destruct H3.
 remember H5 as H13. clear HeqH13.
 apply execcute_s_init in H13. destruct H13.
 exists (x2++x0). split.
 apply star_step with(d1',t').
 assumption.  rewrite app_assoc. rewrite <- H6. assumption.
 exists(x1) . split.
 assert (t0=t0++nil). rewrite app_nil_r. auto.
 rewrite H7. rewrite <- app_assoc. rewrite <- exec_star_inittrace.
 rewrite exec_star_inittrace. rewrite app_nil_r. apply H3.
 rewrite H6 in H1.  rewrite <- app_assoc. rewrite <- H4.
 rewrite <- app_assoc in H1. apply app_inv_head in H1. assumption.
 rewrite H1. auto.
 exists nil. split. rewrite app_nil_r. apply star_refl.
 exists t. split. assumption. simpl. auto.
Qed.

Lemma star_aux_par_left:forall d1 d2 t0 t d1',star red (d1, t0) (d1', t0 ++ t)
                       ->star red (Par d1 d2, t0) (Par d1' d2, t0 ++ t).
Proof.
 intros.
 dependent induction H. apply app_equal_nil in x.  subst. rewrite app_nil_r. apply star_refl. 
 destruct b.
 remember H as H1. clear HeqH1.
 remember H0 as H2. clear HeqH2.
 apply execcute_s_init in H1. destruct H1.
 apply star_exec_s in H2. destruct H2.
 rewrite H2 in H0. rewrite H2.
 apply star_step with (Par s d2,t1).
 constructor. assumption.
 apply IHstar. auto. rewrite H2. auto.
Qed.

Lemma star_aux_par_right:forall d1 d2 t0 t d2',star red (d2, t0) (d2', t0 ++ t)
                       ->star red (Par d1 d2, t0) (Par d1 d2', t0 ++ t).
Proof.
intros.
 dependent induction H. apply app_equal_nil in x.  subst. rewrite app_nil_r. apply star_refl. 
 destruct b.
 remember H as H1. clear HeqH1.
 remember H0 as H2. clear HeqH2.
 apply execcute_s_init in H1. destruct H1.
 apply star_exec_s in H2. destruct H2.
 rewrite H2 in H0. rewrite H2.
 apply star_step with (Par d1 s,t1).
 constructor. assumption.
 apply IHstar. auto. rewrite H2. auto.
Qed.


Lemma interleaveTrace_app_l:forall t t1 t2 t',set_In t (interleaveTrace t1 t2) 
                                        ->set_In (t' ++ t) (interleaveTrace (t' ++ t1) t2).
Proof.
  induction t';intros.
  simpl. assumption. apply IHt' in H. clear IHt'.

  simpl.  destruct t2. rewrite interleaveTrace_nil in H. simpl in H. 
  destruct H. apply app_inv_head in H. subst. 
  simpl. auto. inversion H.

  apply set_union_intro. left. now apply setIn_map.
Qed.

Lemma interleaveTrace_app_r:forall t t1 t2 t',set_In t (interleaveTrace t1 t2) 
                                        ->set_In (t' ++ t) (interleaveTrace t1 (t' ++ t2)).
Proof.
  induction t';intros.
  simpl. assumption. apply IHt' in H. clear IHt'.

  simpl. simpl in H. destruct t1. inversion H. apply app_inv_head in H0. subst.  simpl. auto. inversion H0.
  
  remember (t'++t2). destruct l. simpl. simpl in H. destruct H. 
  rewrite <- H. apply set_add_intro. auto. inversion H.  
  simpl. apply set_union_intro. right. apply setIn_map.
  assumption.
Qed.

Lemma star_aux_par:forall d1 d2 t0 t , star red (Par d1 d2, t0) (Skip, t0 ++ t) ->
                   exists t1, star red (d1,t0) (Skip,t0++t1) /\exists t2,star red (d2,t0) (Skip,t0++t2) /\ set_In t (interleaveTrace t1 t2).


  Proof.
intros.
dependent induction H. inversion H;subst.
assert ((Par d1' d2, t') = (Par d1' d2, t')).
 auto.
 remember H0 as H2. clear HeqH2.
 apply star_exec_s in H2. destruct H2.
apply IHstar with (t2:= x) in H1. destruct H1. destruct H1. destruct H3. destruct H3.
 remember H as H10. clear HeqH10. apply execcute_s_init in H10. destruct H10.
 exists (x2++x0). split.
 apply star_step with (d1',t'). assumption.
 rewrite app_assoc. rewrite <- H6. assumption.
 exists x1. split. 
 assert (t0=t0++nil). rewrite app_nil_r. auto.
 rewrite H7. rewrite <- app_assoc. simpl.
 rewrite <- exec_star_inittrace. rewrite exec_star_inittrace. rewrite app_nil_r. apply H3.   
 rewrite H6 in H2. rewrite <- app_assoc in H2. apply app_inv_head in H2. rewrite H2.
 now apply interleaveTrace_app_l. 
 rewrite H2. auto.

assert ((Par d1 d2', t') = (Par d1 d2', t')).
 auto.
 remember H0 as H2. clear HeqH2.
 apply star_exec_s in H2. destruct H2.
 apply IHstar with (t2:= x) in H1. destruct H1. destruct H1. destruct H3. destruct H3.
 remember H as H10. clear HeqH10. apply execcute_s_init in H10. destruct H10.
 exists x0. split. 
 assert (t0=t0++nil). rewrite app_nil_r. auto.
 rewrite H7. rewrite <- app_assoc. simpl.
 rewrite <- exec_star_inittrace. rewrite exec_star_inittrace. rewrite app_nil_r. apply H1.   
 exists (x2++x1). split.
 apply star_step with (d2',t'). assumption.
 rewrite app_assoc. rewrite <- H6. assumption.
 rewrite H6 in H2. rewrite <- app_assoc in H2. apply app_inv_head in H2. rewrite H2.
 now apply interleaveTrace_app_r. 
 rewrite H2. auto.

 exists nil. split. rewrite app_nil_r. apply star_refl.
 exists t. split. 
 assert (t0=t0++nil). rewrite app_nil_r. auto.
 rewrite H1. rewrite <- app_assoc. simpl.
 rewrite <- exec_star_inittrace. rewrite exec_star_inittrace. rewrite app_nil_r. apply H0.
 simpl. auto.

 exists t. split. 
 assert (t0=t0++nil). rewrite app_nil_r. auto.
 rewrite H1. rewrite <- app_assoc. simpl.
 rewrite <- exec_star_inittrace. rewrite exec_star_inittrace. rewrite app_nil_r. apply H0.
 exists nil. split. rewrite app_nil_r. apply star_refl.
 rewrite interleaveTrace_nil. simpl. auto.
Qed.


Lemma star_aux_aux_aux:forall d d' t0 t1 ,red (d, t0) (d', t1)-> t1 = t0 \/ exists e, t1 = t0++e::nil.
Proof.
  induction d;intros;inversion H;subst.
  left. auto.
  right. exists e. auto.
  left. auto.
  left. auto.
  left. auto.
  left. auto.
  now apply IHd1 in  H1.
  left. auto.
  left. auto.
  left. auto.
  apply IHd1 in H1. assumption.
  apply IHd2 in H1. assumption.
  left. auto.
  left. auto.
Qed.


Lemma star_aux_aux:forall d t0 d' t1 e t, red (d, t0) (d', t1)
                                           -> star red (d', t1) (Skip, t0 ++ e :: t)
                                           -> t1 = t0 \/ t1 = t0++ e::nil.
Proof.
  intros.
  apply star_aux_aux_aux in H. destruct H.
  left. auto.
  destruct H.
  subst. right.
  apply  star_exec_s in H0. destruct H0. 
  rewrite <- app_assoc in H.
  simpl in H.
  apply app_inv_head in H. 
  inversion H. subst. auto.
Qed.

Lemma star_aux: forall d t0 e t,star red (d,t0) (Skip, t0++e::t) 
->exists d', star red (d,t0) (d', t0++ e::nil) /\star red (d', t0++ e::nil)(Skip, t0++e::t).
Proof.
 intros. dependent induction H. SearchAbout(_=_::_->False). apply  app_equal_nil in x.  inversion x.
 destruct b.
  remember H as H10. clear HeqH10.
  apply star_aux_aux with (e:=e)(t:=t) in H10. destruct H10;subst.
  assert ((s, t0) = (s, t0)).
  auto. apply IHstar with (e0:=e)(t2:=t) in H1.
  destruct H1. destruct H1.
  exists x. split. apply star_step with (s,t0); assumption. 
  assumption. 
  auto.
  exists s. split. apply star_step with (s, t0 ++ e :: nil).
  assumption. apply star_refl. assumption.
  assumption.
Qed.

   Lemma map_prefix_nil_false:forall e t, set_In nil (map_prefixo e t) -> False.
   Proof.
    induction t;intros; simpl in H. inversion H. inversion H. inversion H0.
    now apply IHt.
   Qed.

  Lemma inverleave_nil_aux:forall t t', set_In nil (interleaveTrace t t')-> t = nil /\ t'=nil.
  Proof.
   intros.
   destruct t. 
     simpl in H. destruct H. auto. inversion H.
     simpl in H. destruct t'.
       inversion H. inversion H0. inversion H0.
       apply set_union_elim in H. destruct H. apply map_prefix_nil_false in H. inversion H.
       apply map_prefix_nil_false in H. inversion H.
  Qed.
     
 

(*-end of auxilary lemma -*)

Lemma exec_terminates_Aux:
  forall t0 d t', execute_b t0 d t' -> terminates d t0 t'.
Proof.
  unfold terminates.
  induction d.
  (*SKIP*)
  intros; inversion H;subst.
  apply star_refl.
  
  (*EVENT*)
  intros; inversion H;subst.
  apply star_one. apply S_EventExec. 

  (*ALT*) 
  intros; inversion H;subst.
  apply star_step with (b:=(d1,t0)). constructor. apply execute_b_plus_re with(t:=t0) in H4. now apply  IHd1. 
  apply star_step with (b:=(d2,t0)). constructor. apply execute_b_plus_re with(t:=t0) in H4. now apply IHd2.
  
  (*OPT*)
  intros; inversion H;subst.
  apply star_step with (b:=(d,t0)). constructor. apply execute_b_plus_re with(t:=t0) in H2. now apply IHd.
  apply star_step with (b:=(Skip,t')). constructor. apply star_refl.

  (*STRICT*)
   intros; inversion H;subst.
   apply star_trans with (b:=(Strict Skip d2,t0++t)).
   apply star_red_seq_left. apply execute_b_plus_re with(t:=t0) in H2. now apply IHd1.
   apply star_step with (d2,t0++t). constructor. apply execute_b_plus_re with(t:=t0) in H4.
   apply IHd2 in H4. apply exec_star_inittrace. 
   assert (t = t++nil). rewrite app_nil_r . auto.
   rewrite H0. rewrite <- app_assoc. apply exec_star_inittrace. simpl.
   rewrite exec_star_inittrace. rewrite app_nil_r. apply H4. 

  (*LOOP*)
   induction n.
   intros. inversion H. subst.
   eapply star_step; constructor.
   intros.  inversion H. subst. apply star_step with (Strict d (Loop n d),t0).
   constructor.
   apply execute_b_plus_re with(t:=t0) in H3. apply IHd in H3.
   simpl. 
   apply star_trans with (Strict Skip (Loop n d), t0++t).
   apply star_red_seq_left. assumption.
   apply star_step with (Loop n d, t0++t). constructor.  apply exec_star_inittrace.
   apply execute_b_plus_re with(t:=t0) in H5. apply IHn in H5.
   assert (t = t++nil). rewrite app_nil_r . auto.
   assert (t0 = t0++nil). rewrite app_nil_r . auto.
   rewrite H0. rewrite H1 in H5. rewrite <- app_assoc. rewrite <- app_assoc in H5.
   rewrite <- exec_star_inittrace in H5. rewrite <- exec_star_inittrace. assumption.

  (*PAR*)
  intros. inversion H. subst. clear H.
(*induction t''*)
  apply execute_b_plus_re with (t:=t0) in H2. apply IHd1 in H2.
  apply execute_b_plus_re with(t:=t0) in H4. apply IHd2 in H4.
  clear IHd1 IHd2 .
  revert d1 d2 t t'0 t0 H2 H4 H6. 
 
  induction t'';intros.
  apply inverleave_nil_aux in H6. destruct H6. subst.
  apply star_trans with(Par Skip d2,t0++nil).
  now apply star_aux_par_left.
  apply star_step with (d2,t0++nil).
  constructor. rewrite app_nil_r. rewrite app_nil_r in H4. assumption.
  
  remember H6 as H10. clear HeqH10.
  apply interleaveTrace_app_rev in H6. destruct H6. destruct H; destruct H;subst. 
 remember H2 as H20. clear HeqH20. 
 apply star_aux in H2. destruct H2.
 apply star_trans with (Par x0 d2,t0++a::nil). 
 now apply star_aux_par_left.
 assert (t0 ++ a :: t'' = (t0++a::nil)++t'').
 rewrite <- app_assoc. simpl. auto. 
 rewrite H1.
 apply IHt'' with (d1:=x0)(t0:=t0++a::nil)(t:=x)(t'0:=t'0).
 rewrite <- app_assoc. simpl. destruct H. assumption. 
 assert (t0 ++ a :: nil = (t0 ++ a :: nil) ++nil).
 rewrite <- app_assoc. simpl. auto. 
 rewrite H2. rewrite <- app_assoc. rewrite <- app_assoc.  rewrite <- exec_star_inittrace.
 rewrite <- exec_star_inittrace. rewrite exec_star_inittrace. rewrite app_nil_r. apply H4. 
 assert (a::t'' = (a::nil)++t'').
 simpl. auto.
 assert (a::x = (a::nil)++x).
 simpl. auto.
 now apply interleaveTrace_aux with (e:=a). 


 subst.
 remember H4 as H20. clear HeqH20. 
 apply star_aux in H4. destruct H4.
 apply star_trans with (Par d1 x0,t0++a::nil). 
 now apply star_aux_par_right.
 assert (t0 ++ a :: t'' = (t0++a::nil)++t'').
 rewrite <- app_assoc. simpl. auto. 
 rewrite H1.
 apply IHt'' with (d1:=d1)(d2:=x0)(t0:=t0++a::nil)(t:=t)(t'0:=x).
 assert (t0 ++ a :: nil = (t0 ++ a :: nil) ++nil).
 rewrite <- app_assoc. simpl. auto. 
 rewrite H3. rewrite <- app_assoc. rewrite <- app_assoc.  rewrite <- exec_star_inittrace.
 rewrite <- exec_star_inittrace. rewrite exec_star_inittrace. rewrite app_nil_r. apply H2. 
 rewrite <- app_assoc. simpl. destruct H. assumption. 
 now apply interleaveTrace_aux_r with (e:=a). 
Qed.

Lemma exec_terminates:
  forall d t', execute_b nil d t' -> terminates d nil t'.
Proof.
 apply exec_terminates_Aux.
Qed.
(*-end of theorem 3-*)


(*-Proof of theorem 4-*)
(*-Auxilary lemma of theorem 4 -*)

Lemma appendstrict: forall t d t' ,execute_b t d t' -> exists  t'',execute_b t d (t++t'') /\ t'= t++t''.
Proof.
  induction d;intros;inversion H;subst.
  
  (*SKIP*)
   exists nil. split. rewrite app_nil_r. constructor.  rewrite app_nil_r.  auto.

   (*EVENT*)
   exists (e :: nil).  auto. 

   (*ALT*)
    exists t0. auto. 
    exists t0. auto.

   (*OPT*)
    exists t0. auto. 
    exists nil. split. rewrite app_nil_r. constructor.  rewrite app_nil_r.  auto.
  
   (*STRICT*)
    exists (t0++t'0). auto. 

   (*LOOP*)
   exists (t0 ++ t''). auto. 
   exists nil. split. rewrite app_nil_r. constructor.  rewrite app_nil_r.  auto.

   (*PAR*)
   exists (t''). split. assumption. auto.
Qed.


Lemma appendini: forall (t : Trace) (t0 : list Event) (d : SeqDiag) (t' : list Event),
  execute_b t d t' -> exists t'' : list Event, t' = t ++ t''.
Proof.
  induction d;intros;inversion H;subst.
  (*SKIP*)
  exists nil. rewrite app_nil_r. auto.
  (*EVENT*)
  exists (e::nil).  auto.
  (*ALT1*)
  exists t1. auto.
  (*ALT2*)
  exists t1. auto.
  (*OPT*)
  exists t1. auto.
  (*OPTSKIP*)
  exists nil. rewrite app_nil_r. auto.
  (*STRICT*)
  exists (t1++t'0). auto.
  (*LOOPN*)
  exists (t1++t''). auto.
  (*LOOP0*)
  exists nil. rewrite app_nil_r. auto.
  (*PAR*)
  exists t''. auto.
Qed.

  
Lemma red_preserves_exec:
  forall d t d' t',  red (d, t) (d', t') ->
  forall tfinal, execute_b t' d' tfinal -> execute_b t d tfinal.
Proof.

 induction d.

  (*SKIP*)
  intros. inversion H;subst. inversion H0;subst. constructor.
  
  (*EVENT*)
   intros. inversion H;subst. inversion H0;subst. constructor.

  (*ALT*) 
  intros. inversion H;subst.  inversion H0;subst; try apply execute_b_plus in H0;repeat constructor;auto. 
  rewrite <- app_nil_r. repeat constructor.
  rewrite <- app_nil_r .  repeat constructor. 

inversion H0;subst;try apply execute_b_plus in H0;try apply AltExec2;auto.
  rewrite <- app_nil_r. apply B_AltExec1. constructor.
 rewrite <- app_nil_r. rewrite app_nil_r. apply appendstrict in H0. destruct H0. destruct H0. rewrite H1. apply B_AltExec2 . 
 apply execute_b_plus in H0 .  assumption.

  (*OPT*)
   intros. inversion H;subst. inversion H0;subst; constructor;try  now apply execute_b_plus in H0. 
   inversion H0;subst. constructor.

  (*STRICT*)
   intros. inversion H;subst.


   inversion H0;subst.
   apply IHd1 with (tfinal:=t' ++ t0)  in H2.

   apply appendstrict in H2. destruct H2. destruct H1.
  rewrite app_assoc. rewrite H2. rewrite <-app_assoc.
  apply B_StrictExec with(t:=x)(t':=t'0).
   apply execute_b_plus in H1. assumption. assumption. auto.
  apply execute_b_plus_re. assumption.
 
   apply appendstrict in H0. destruct H0. destruct H0. subst.
   apply  B_StrictExec with (t:=nil)(t':=x). constructor. apply execute_b_plus in H0. assumption. auto.

   (*LOOP*)
   induction n;intros.
   inversion H;subst. inversion H0;subst. constructor. 
   inversion H;subst. inversion H0;subst. now apply B_LoopExec. 

   (*PAR*)
   intros. inversion H;subst.

   inversion H0. subst.
   remember H2 as H10. clear HeqH10.
   remember H2 as H11. clear HeqH11.
   apply execcute_s_init in H11. destruct H11. subst.
   apply IHd1 with (tfinal:=t++x ++ t0)  in H2.
   rewrite <- app_assoc. apply B_ParExec with (t:=x++t0)(t':=t'0).
   assert (t = t++nil). rewrite app_nil_r . auto.
   apply IHd1 with (d':=d1')(t':=x). 
   rewrite H1 in H10. rewrite <- app_assoc in H10.
   rewrite <-  exec_inittrace in H10. assumption. apply execute_b_plus_re. assumption.
   assumption.
   now apply interleaveTrace_app_l.
   rewrite app_assoc.
   apply execute_b_plus_re. assumption.

   inversion H0. subst.
   remember H2 as H10. clear HeqH10.
   remember H2 as H11. clear HeqH11.
   apply execcute_s_init in H11. destruct H11. subst.
   apply IHd2 with (tfinal:=t++x ++ t'0)  in H2.
   rewrite <- app_assoc. apply B_ParExec with (t:=t0)(t':=x++t'0). 
   assumption.
   assert (t = t++nil). rewrite app_nil_r . auto.
   apply IHd2 with (d':=d2')(t':=x). 
   rewrite H1 in H10. rewrite <- app_assoc in H10.
   rewrite <-  exec_inittrace in H10. assumption. apply execute_b_plus_re. assumption.
   now apply interleaveTrace_app_r.
   rewrite app_assoc.
   apply execute_b_plus_re. assumption.

   remember H0 as H10. clear HeqH10.
   apply appendini in H0.  destruct H0. subst.
   apply B_ParExec with (t:=nil) (t':=x). constructor.
   apply execute_b_plus in H10. assumption.
   simpl. auto. apply tfinal.

   remember H0 as H10. clear HeqH10.
   apply appendini in H0.  destruct H0. subst.
   apply B_ParExec with (t:=x) (t':=nil). 
   apply execute_b_plus in H10. assumption. constructor.
   rewrite interleaveTrace_nil. simpl. auto. apply tfinal.
 Qed.

Lemma terminates_exec_Aux:
  forall t0 d t', terminates d t0 t' -> execute_b t0 d t'.
Proof.
  unfold terminates. intros. dependent induction H.
(* base case *)
  constructor.
(* step case *)
  destruct b. eapply red_preserves_exec. eauto.  eauto.
Qed.

(*-end of auxilary lemma -*)

Lemma terminates_exec:
  forall d t', terminates d nil t' -> execute_b nil d t'.
Proof.
  intros. now apply terminates_exec_Aux.
Qed.
(*-end of theorem 4-*)


(*--Equvilance of Denotation semantic and Big-step Operational semantic--*)

(*-Proof of theorem 5 -*)
(*-Auxilary lemma of theorem 5 -*)
Lemma strict_aux_map: forall (t1 t2:Trace) s ,set_In t2 s -> set_In (t1++t2) (map (app t1) s).
Proof.
 intros.
 induction s.
inversion H.
 simpl in H. destruct H. 
  rewrite H. simpl. left. auto.
  simpl. right. apply IHs. assumption.
Qed.

Lemma strictsnd_aux:forall t1 t2 s1 s2 ,set_In t1 s1 ->set_In t2 s2 -> set_In (t1 ++ t2) (unionModel s1 s2).
Proof.
 intros.
 induction s5;induction s6.

 inversion H.  inversion H. inversion H0.
 simpl in H. simpl in H0. destruct H;destruct H0.
 rewrite H; rewrite H0.
 simpl. apply set_union_intro1. simpl. left. auto.
   rewrite H. simpl. apply set_union_intro1. 
   simpl. right. apply in_map.  assumption.
   rewrite H0. rewrite H0 in IHs5. simpl. apply set_union_intro2. unfold unionModel. apply IHs5. assumption.
   simpl. apply set_union_intro2. apply IHs5. assumption.
Qed.

Lemma map_app_aux: forall (t:Trace) t' s ,set_In t' s -> set_In (t ++ t') (map (app t) s).
Proof.
induction s;intros.
 inversion H. simpl in H. destruct H. subst. simpl.  left. auto. 
 apply IHs in H. simpl. right. auto.
Qed.

  Lemma loopsnd_aux:forall m1 m2 t' t,set_In t m1 ->  set_In t' m2 ->set_In (t ++ t') (LoopStrictAux m1 m2).
  Proof.
   induction m1. intros.
     inversion H.
     intros. simpl in H. destruct H. 
      rewrite H. simpl. subst.  apply set_union_intro1.  now apply map_app_aux.
      simpl. apply  set_union_intro2. 
      now apply IHm1.
  Qed.


  Lemma par_aux:forall m1 m2 t' t t'',set_In t m1 ->  set_In t' m2 
                         -> set_In t'' (interleaveTrace t t')
                         -> set_In t'' (interleaveModel m1 m2).
  Proof.
  induction m1;intros.
  inversion H.
  simpl in H.  destruct H.
   subst. simpl. apply set_union_intro. left. clear IHm1.
   induction m2. inversion H0.
   simpl. simpl in H0. 
    destruct H0;  apply set_union_intro; simpl.
    left. subst. assumption.
    right. now apply IHm2.
   simpl. apply set_union_intro. right. now apply IHm1 with(t:=t)(t':=t').
  Qed.
(*-end of auxilary lemma -*)

Theorem Soundness: forall d t, 
execute_b nil d t -> set_In t (interp d).
Proof.

  
  induction d.
  
  (*SKIP*)
  intros. inversion H;subst.
  simpl. left. reflexivity.

  (*EVENT*)
  intros. inversion H;subst.
  simpl. left. reflexivity.
  
  (*ALT*)
   intros. inversion H;subst.
   apply IHd1 in H4. simpl. apply set_union_intro1 . assumption.
   apply IHd2 in H4. simpl. apply set_union_intro2 . assumption.

  (*OPT*)
   intros. inversion H;subst.
     apply IHd in H2. simpl. apply set_union_intro2 . assumption.
     simpl.  apply set_union_intro1 . simpl. left. reflexivity.
   
  
  (*STRICT*)
  intros. inversion H;subst.
  simpl. apply IHd1 in H2. apply IHd2 in H4.
  apply strictsnd_aux; assumption.

  (*LOOP*)
   induction n;intros.
  inversion H;subst.  simpl. left. auto.
  inversion H;subst. simpl.
  apply IHd in H3.
  apply IHn in H5. simpl in H5.
  now apply loopsnd_aux.

 (*PAR*)
  intros. inversion H;subst.
  simpl. apply IHd1 in H2. apply IHd2 in H4. clear- H2 H4 H6.
  now apply par_aux with(t:=t0)(t':=t').
Qed.
(*-end of theorem 5 -*)



(*-Proof of theorem 6 -*)
(*-Auxilary lemma of theorem 6 -*)
Lemma unionmodel_aux: forall m,unionModel m nil = nil.
Proof.
intro m.
induction m.
simpl. reflexivity.
simpl. rewrite IHm.  simpl. auto.
Qed.

Lemma strictcmp_aux :forall s1 s2 (t:Trace),
  set_In t (unionModel s1 s2) -> exists t1,exists t2,set_In t1 s1 /\ set_In t2 s2 /\ t=t1++t2.
Proof.
  intros.
   induction s5;destruct s6.
   simpl in H. inversion H.
   simpl in H. inversion H.
   simpl in H. rewrite unionmodel_aux in H. simpl in H. inversion H.  
   
   simpl in H. apply set_union_elim  in H. destruct H.
   simpl in H. destruct H.
     exists a. exists t0.
    split;simpl. left. auto. split. left. auto. rewrite H. auto.
     exists a. apply in_map_iff in H. destruct H. destruct H.
     exists x. simpl. split. left. auto. split. right. auto. apply eq_sym. auto.
   apply IHs5 in H. destruct H. destruct H. destruct H. destruct H0.
     exists x. exists x0.  split. simpl. right. auto. split.  auto. auto.
Qed.

Lemma map_app_exists_aux: forall t (a:Trace) s,set_In t (map (app a) s) -> exists t', set_In t' s /\ t = a++t'.
Proof.
     induction s.
     intros. inversion H.
     intros. simpl in H. destruct H. subst. exists a0. simpl. auto.
     apply IHs in H. destruct H. destruct H. subst. exists x. simpl. auto.
Qed.
      

 Lemma  loopcmp_aux: forall t m1 m2, set_In t (LoopStrictAux m1 m2) -> exists t1,exists t2,set_In t1 m1 /\ set_In t2 m2/\ t = t1++t2.
    Proof.
    induction m1.
    intros. inversion H.
    intros.  simpl in H.  apply set_union_elim in H. destruct H.
    exists a. apply map_app_exists_aux in H. destruct H. destruct H. subst. exists x. simpl. auto.
    apply IHm1 in H. destruct H. destruct H. exists x. exists x0. repeat destruct H. simpl.  auto.
Qed.


Lemma parcmp_aux:forall t m1 m2 ,set_In t (interleaveModel m1 m2) ->
                      exists t1, exists t2,set_In t1 m1 /\ set_In t2 m2/\ set_In t (interleaveTrace t1 t2).
    Proof.
    induction m1;intros.
     inversion H.
     simpl in H. apply set_union_elim in H. destruct H.
     exists a. clear IHm1. 
     induction m2. inversion H.
     simpl in H. apply set_union_elim in H. destruct H.
     exists a0. split;simpl;auto.
     apply IHm2 in H. destruct H. destruct H. destruct H0.
     exists x. split;simpl;auto. 
    apply IHm1 in H. destruct H. destruct H. destruct H. destruct H0.
    exists x. exists x0. 
    split. simpl. right. assumption. 
    split. simpl. assumption.
    assumption.
Qed.    

(*-end of auxilary lemma -*)

Theorem Completeness :forall d t ,
      set_In t (interp d)
      ->  execute_b nil d t .
Proof.
    
    induction d.

   (*SKIP*)
    intros. inversion H;subst. constructor. inversion H0.
   (*EVENT*)
    intros. inversion H;subst. constructor. inversion H0.
    (*ALT*)
   intros. simpl in H. apply set_union_elim in H. destruct H.
     apply IHd1 in H. rewrite <- app_nil_l. apply B_AltExec1. assumption.
     apply IHd2 in H. rewrite <- app_nil_l. apply B_AltExec2. assumption.
   (*OPT*)
   intros. simpl in H. apply set_union_elim in H. destruct H.
     inversion H;subst. apply B_OptExec2. inversion H0.
     apply IHd in H. rewrite <- app_nil_l. apply B_OptExec1. assumption.
   (*STRICT*)
    intros. simpl in H. apply strictcmp_aux in H. destruct H. destruct H. destruct H. destruct H0.
    rewrite <- app_nil_l. apply B_StrictExec with (t:= x)(t':=x0). apply IHd1. assumption. apply IHd2. assumption. assumption.
   (*LOOP*)
    induction n.
    intros.  inversion H;subst. constructor. inversion H0.
    intros.  simpl in H.  apply loopcmp_aux in H. repeat destruct H.
    destruct H0. apply IHd in H. apply IHn in H0. subst. rewrite <- app_nil_l. now apply B_LoopExec. 
   (*PAR*)
   intros. simpl in H. apply parcmp_aux in H.  destruct H. destruct H. destruct H. destruct H0.
   apply IHd1 in H. rewrite <- app_nil_l. 
   apply IHd2 in H0. apply B_ParExec with (t:=x)(t':=x0); assumption.     
Qed.
(*-end of theorem 6-*)



 
(*Definition of an Example*)
(*--Lifeline--*)
Definition l_user:= 100.
Definition l_server:= 200.

(*--Message--*)
Definition m_id:=(0,l_user,l_server).
Definition m_pwd:=(1,l_user,l_server).
Definition m_loginsucc:=(2,l_server,l_user).
Definition m_loginfail:=(3,l_server,l_user).
Definition m_cmd:=(4,l_user,l_server).

Definition sid := (!,m_id).
Definition rid :=(?,m_id).
Definition spwd := (!,m_pwd).
Definition rpwd :=(?,m_pwd).
Definition sloginsucc := (!,m_loginsucc).
Definition rloginsucc :=(?,m_loginsucc).
Definition sloginfail := (!,m_loginfail).
Definition rloginfail :=(?,m_loginfail).
Definition scmd := (!,m_cmd).
Definition rcmd :=(?,m_cmd).

Definition exdiagram := 
Strict (Strict (Strict (E sid) (E rid)) (Strict (E spwd) (E rpwd)))
(Alt (Strict (Strict (E sloginsucc) (E rloginsucc)) 
(Opt (Strict (E scmd) (E rcmd)))) (Strict (E sloginfail) (E rloginfail))).

Definition t:= sid::rid::spwd::rpwd::sloginsucc::rloginsucc::scmd::rcmd::nil.

Compute  interp exdiagram. 

Theorem test:terminates exdiagram nil t.
Proof.
  unfold terminates. unfold exdiagram. unfold t.
  apply star_trans with (Strict Skip (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail))),sid
  :: rid :: spwd :: rpwd::nil).
   apply star_step with (Strict (Strict (Strict Skip (E rid)) (Strict (E spwd) (E rpwd)) ) (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail))),sid:: nil).
   constructor. constructor. constructor. constructor.
   apply star_step with (Strict (Strict (E rid) (Strict (E spwd) (E rpwd)) ) (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail))),sid:: nil).
   constructor. constructor. constructor.
  apply star_step with (Strict (Strict Skip (Strict (E spwd) (E rpwd)) ) (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail))),sid::rid:: nil).
  constructor. constructor. constructor.
  apply star_step with (Strict (Strict (E spwd) (E rpwd))  (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail))),sid::rid:: nil).
    constructor. constructor. 
    apply star_step with (Strict (Strict Skip (E rpwd))  (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail))),sid::rid::spwd:: nil).
    constructor. constructor.  constructor. 
    apply star_step with (Strict (E rpwd) (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail))),sid::rid::spwd:: nil).
    constructor. constructor.
    apply star_step with (Strict Skip (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail))),sid::rid::spwd::rpwd:: nil).
    constructor. constructor.
    apply star_refl.
    apply star_step with (Alt
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))))
        (Strict (E sloginfail) (E rloginfail)),sid::rid::spwd::rpwd:: nil).
    constructor.
    apply star_step with 
        (Strict (Strict (E sloginsucc) (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))),sid::rid::spwd::rpwd:: nil).
    constructor.
    apply star_step with 
        (Strict (Strict Skip (E rloginsucc))
           (Opt (Strict (E scmd) (E rcmd))),sid::rid::spwd::rpwd::sloginsucc:: nil).
    constructor. constructor. constructor.
   apply star_step with 
        (Strict (E rloginsucc)
           (Opt (Strict (E scmd) (E rcmd))),sid::rid::spwd::rpwd::sloginsucc:: nil).
    constructor. constructor. 
     apply star_step with 
        (Strict Skip
           (Opt (Strict (E scmd) (E rcmd))),sid::rid::spwd::rpwd::sloginsucc::rloginsucc:: nil).
    constructor. constructor. 
     apply star_step with 
        (Opt (Strict (E scmd) (E rcmd)),sid::rid::spwd::rpwd::sloginsucc::rloginsucc:: nil).
    constructor.
    apply star_step with 
        (Strict (E scmd) (E rcmd),sid::rid::spwd::rpwd::sloginsucc::rloginsucc:: nil).
    constructor.
   apply star_step with 
        (Strict Skip (E rcmd),sid::rid::spwd::rpwd::sloginsucc::rloginsucc::scmd:: nil).
    constructor. constructor.
      apply star_step with 
         (E rcmd,sid::rid::spwd::rpwd::sloginsucc::rloginsucc::scmd:: nil).
    constructor. 
      apply star_step with 
         (Skip,sid::rid::spwd::rpwd::sloginsucc::rloginsucc::scmd::rcmd:: nil).
    constructor. 
   apply star_refl.
Qed.







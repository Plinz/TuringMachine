(* Michaël PÉRIN, Verimag / Université Grenoble-Alpes, Février 2017 
 *
 * Part of the project TURING MACHINES FOR REAL
 *
 * Some Turing Machines
 *
 *)


  
open Alphabet
open State
open Pattern
open Symbol
open Action
open Transition
open Html
open Pretty


module Turing_Machine =
  (struct

    type t = turing_machine
	  
    let (nop: t) = { name = "" ;
		     nb_bands = 1 ;
		     initial = State.initial ; accept = State.accept ; reject = State.reject ;
		     transitions = [ (State.initial, Action(Nop), State.accept)]
		   }
	
    let (finalize: string -> turing_machine -> turing_machine) = fun name tm ->
	  { tm with name = name }

    let (sequence: Instruction.t list -> turing_machine) = fun instructions ->
	  let init = nop.initial and accept = nop.accept in
	    { nop with
	      name = Instruction.to_ascii (Seq instructions) ;
	      transitions = [ (init, Seq instructions, accept) ]	    
	    }

    (* PRETTY PRINTING *)

    let (to_ascii: turing_machine -> string) = fun tm -> tm.name

    let (to_html: Html.options -> turing_machine -> Html.content) = fun _ tm -> Html.italic (to_ascii tm)
	    
    (* user *)
	    
    let (pretty: t -> string) =
      match Pretty.get_format() with
      | Pretty.Html  -> (to_html [])
      | Pretty.Ascii -> to_ascii
		
		
    (* IMPERATIVE FEATURES for reusing existing turing machine *) 	    
		
    class collection_of_turing_machine =
      object
	val mutable collection: turing_machine list = []
	    
	method add: turing_machine -> unit = fun tm ->
	      collection <- tm::collection 
				  
	method find: string -> turing_machine = fun name ->
	      match List.filter (fun tm -> tm.name = name) collection with
	      | [tm] -> tm
	      | [] -> let error_msg = String.concat "" [ "Turing_Machine.collection_of_turing_machine #find: TM " ; name ; " not found in the library." ] in failwith error_msg
	      | _  -> let error_msg = String.concat "" [ "Turing_Machine.collection_of_turing_machine #find: Multiple TM " ; name ; " in the library."  ] in failwith error_msg
      end
	
	
    let object_TM_library = new collection_of_turing_machine
	
    let (i_make: string -> turing_machine -> turing_machine) = fun name turing_machine ->
	  let tm = finalize name turing_machine in
	    begin
	      object_TM_library#add tm ;
	      tm
	    end
	      
    let (i_find_tm_named: string -> turing_machine) = fun name ->
	  object_TM_library#find name
	    
	    
	    
    (* A COLLECTION OF BASIC TM *)
	    
    let (move: Moving.t -> turing_machine) = fun direction ->
	  let init = nop.initial and accept = nop.accept in
	    { nop with
	      name = String.concat "_" [ "move" ; Moving.to_ascii direction ] ;
	      transitions = [ (init, Action(RWM(Match(ANY), No_Write, direction)), accept) ]
	    }
	    
    let (find_symbol_on_the: Symbol.t -> Moving.t -> turing_machine) = fun symbol direction ->
	  let
	      tm_name = String.concat "_" [ Symbol.verbatim symbol ; "on_the" ; Moving.to_ascii direction ]
	  in
	  let init = nop.initial and accept = nop.accept in
	    finalize tm_name
	      { nop with
		transitions =
 		[ (init, Action(RWM(Match(BUT symbol), No_Write, direction)), init) ;
		  (init, Action(RWM(Match(VAL symbol), No_Write, Here)), accept)
		]
	      }
	      
    let (first_blank_on_the: Moving.t -> turing_machine) = find_symbol_on_the B 
      
    let (second_blank_on_the: Moving.t -> turing_machine) = fun direction ->
	  let init = nop.initial and accept = nop.accept in
	    { nop with
	      name = String.concat "_" [ "second_blank_on_the" ; Moving.to_ascii direction ] ;
	      transitions = [ (init, Seq [ Run (first_blank_on_the direction) ; Action(RWM(Match(ANY),No_Write, direction)) ; Run (first_blank_on_the direction) ], accept) ] 
	    }

    let (goto_right_blank:  turing_machine) = find_symbol_on_the B Right

    let (goto_right_dollar: turing_machine) = find_symbol_on_the D Right 
    

    let (most_on_the: Moving.t -> turing_machine) = fun dir ->
	  let rid =
	    (match dir with
	    | Left -> Right
	    | Right -> Left
	    )
	  in
	    let init = nop.initial and accept = nop.accept in let loop = State.fresh_from init in	      
	      { nop with
		transitions = [ (init, Action( RWM (Match(ANY), No_Write, dir)), loop) ;
				(loop, Action(RWM(Match(BUT B), No_Write, dir)), loop) ;
				(loop, Action(RWM(Match(VAL B), No_Write, rid)), accept)			    
			      ]
	      }

    let (right_most: turing_machine) = finalize ">?B" (most_on_the Right)

    let (left_most:  turing_machine) = finalize "B?<" (most_on_the Left)

    let (erase: turing_machine) = 
      let init = nop.initial and accept = nop.accept in let loop = State.fresh_from init in	
	{ nop with
	  name = "erase" ;
	  transitions =
 	  [ (init, Run right_most, loop) ;
	    (loop, Action( RWM (Match(BUT B), Write B,  Left)), loop) ;
	    (loop, Action( RWM (Match(VAL B), No_Write, Here)), accept)
	  ]
	}
	
    let (erase_backward: turing_machine) = 
      let init = nop.initial and accept = nop.accept in let loop = State.fresh_from init in	
	{ nop with
	  name = "<erase" ;
	  transitions =
 	  [ (init, Action( RWM (Match(ANY)  , Write B , Left )), loop) ;
	    (loop, Action( RWM (Match(BUT B), Write B , Left )), loop) ;
	    (loop, Action( RWM (Match(VAL B), No_Write, Right)), accept)
	  ]
	}
	
    let (incr: turing_machine) =
      let init = nop.initial and accept = nop.accept in 	
	{ nop with
	  name =  "incr" ; 
	  transitions = 
 	  [ (init, Action(RWM(Match(VAL U), Write Z, Right)), init) ;
	    (init, Action(RWM(Match(VAL Z), Write U, Here )), accept) ; 
            (init, Action(RWM(Match(VAL B), Write U, Here )), accept) 
	  ]
	}


    let (decr: turing_machine) =
      let init = nop.initial and accept = nop.accept and reject = nop.reject in
 	let unit = State.fresh_from init in
	  let zero = State.fresh_from unit in
	    let back = State.fresh_from zero in
	      { nop with
		name = "decr" ;
		transitions = 
		[ (init, Action( RWM (Match(VAL Z), No_Write, Right)), unit) ;
		  (init, Action( RWM (Match(VAL U), Write Z , Here )), accept) ;
		  (init, Action( RWM (Match(VAL B), No_Write, Here )), reject) ;
		  
		  (unit , Action( RWM (Match(VAL B), No_Write, Left )), reject) ;
		  (unit , Action( RWM (Match(VAL Z), No_Write, Right)), unit) ;
		  (unit , Action( RWM (Match(VAL U), Write B , Right)), zero) ;
		  
		  (zero , Seq [ Action( RWM (Match(VAL B), No_Write, Left)) ; Action( RWM (Match(VAL B), No_Write, Left)) ], back) ;
		  (zero , Seq [ Action( RWM (Match(BUT B), No_Write, Left)) ; Action( RWM (Match(VAL B), Write  Z, Left)) ], back) ;
		  
		  (back , Action( RWM (Match(VAL Z), Write U , Left )), back) ;
		  (back , Action( RWM (Match(VAL B), No_Write, Right)), accept) 
		]
	      }
		
    let (generic_dup: symbols -> turing_machine) = fun symbols ->
	  let init = nop.initial and accept = nop.accept in	  
	    let generic_transitions =
	      Transition.foreach_symbol_of symbols (OUT [B;D]) (fun s ->
		    [ (init     , Action(RWM(Match(VAL(s)), Write B, Right)) , Qs(1,[s])) ; 
		      (Qs(1,[s]), Run(second_blank_on_the Right), Qs(2,[s])) ; 
		      (Qs(2,[s]), Action(RWM(Match(VAL(B)), Write s, Here)) , Qs(3,[s])) ;
		      (Qs(3,[s]), Run (second_blank_on_the Left)            , Qs(4,[s])) ; 
		      (Qs(4,[s]), Action(RWM(Match(VAL(B)), Write s, Right)), init)
		    ])
	    in 
	      { nop with
		name = "dup_" ^ (Pretty.set Symbol.to_ascii symbols) ;
		transitions = generic_transitions
		@ [ (init, Action(RWM(Match(VAL B), Write D, Here)), accept) ] 
	      }
	    
	
    let (generic_swap: symbols -> turing_machine) = fun symbols ->
	  let init = nop.initial and accept = nop.accept in	  
	    let generic_transitions =
	      Transition.foreach_symbol_of symbols ANY (fun s ->
		    Transition.foreach_symbol_of symbols ANY (fun l ->
			  [ (init     , Action( RWM (Match(VAL(s)), Write B, Right)), Qs(1,[s])) ; 
			    (Qs(1,[s]), Action( RWM (Match(VAL(l)), Write s, Left )), Qs(2,[l])) ;
			    (Qs(2,[l]), Action( RWM (Match(VAL(B)), Write l, Right)), accept)
			  ]))
	    in 
	      { nop with
		name = "swap_" ^ (Pretty.set Symbol.to_ascii symbols) ; 
		transitions = generic_transitions
	      }

    (* The busy beavers     : https://en.wikipedia.org/wiki/Busy_beaver
     * Les castors affairés : https://fr.wikipedia.org/wiki/Castor_affairé 
     *)

    let (bb4: turing_machine) = 
      let z = Bit.zero and u = Bit.unit in
	let init = nop.initial and accept = nop.accept in
	  { nop with
	    name = "BB4_stops_after_107_steps" ;
	    transitions = 
	    [ (init, Action( RWM (Match(VAL z), Write u, Right)), Q 2) ;
	      (init, Action( RWM (Match(VAL u), Write u, Left )), Q 2) ;
	      (Q 2, Action( RWM (Match(VAL z), Write u, Left )), init) ;
	      (Q 2, Action( RWM (Match(VAL u), Write z, Left )), Q 3) ;
	      (Q 3, Action( RWM (Match(VAL z), Write u, Here )), accept) ;
	      (Q 3, Action( RWM (Match(VAL u), Write u, Left )), Q 4) ;
	      (Q 4, Action( RWM (Match(VAL z), Write u, Right)), Q 4) ;
	      (Q 4, Action( RWM (Match(VAL u), Write z, Right)), init) 
	    ] 
	  }
	    
    let (bb5: turing_machine) = 
      let z = Bit.zero and u = Bit.unit in
	let init = nop.initial and accept = nop.accept in	    
	  { nop with
	    name = "BB5_stops_after_47_176_870_steps" ;
	    transitions = 
	    [ (init, Action( RWM (Match(VAL z), Write u, Left )), Q 2) ;
	      (init, Action( RWM (Match(VAL u), Write u, Right)), Q 3) ;
	      (Q 2, Action( RWM (Match(VAL z), Write u, Left )), Q 3) ;
	      (Q 2, Action( RWM (Match(VAL u), Write u, Left )), Q 2) ;
	      (Q 3, Action( RWM (Match(VAL z), Write u, Left )), Q 4) ;
	      (Q 3, Action( RWM (Match(VAL u), Write z, Right)), Q 5) ;
	      (Q 4, Action( RWM (Match(VAL z), Write u, Right)), init) ;
	      (Q 4, Action( RWM (Match(VAL u), Write u, Right)), Q 4) ;
	      (Q 5, Action( RWM (Match(VAL z), Write u, Here )), accept) ;
	      (Q 5, Action( RWM (Match(VAL u), Write z, Right)), init) 	    
	    ] 
	  }

	
    let (bb6: turing_machine) = 
      let z = Bit.zero and u = Bit.unit in
	let init = nop.initial and accept = nop.accept in	          
	  { nop with
	    name = "BB6_discovered_in_june_2010_stops_after_3.515_*_10^18267_steps" ;
	    transitions = 
	    [ (init, Action( RWM (Match(VAL z), Write u, Right)), Q 2) ;
	      (init, Action( RWM (Match(VAL u), Write u, Left )), Q 5) ;
	      (Q 2, Action( RWM (Match(VAL z), Write u, Right)), Q 3) ;
	      (Q 2, Action( RWM (Match(VAL u), Write u, Right)), Q 6) ;
	      (Q 3, Action( RWM (Match(VAL z), Write u, Left )), Q 4) ;
	      (Q 3, Action( RWM (Match(VAL u), Write z, Right)), Q 2) ;
	      (Q 4, Action( RWM (Match(VAL z), Write u, Right)), Q 5) ;
	      (Q 4, Action( RWM (Match(VAL u), Write z, Left )), Q 3) ;
	      (Q 5, Action( RWM (Match(VAL z), Write u, Left )), init) ;
    	      (Q 5, Action( RWM (Match(VAL u), Write z, Right)), Q 4) ;
	      (Q 6, Action( RWM (Match(VAL z), Write u, Left )), accept) ;
	      (Q 6, Action( RWM (Match(VAL u), Write z, Right)), Q 3) 	    
	    ] 
	  }

    (* BB 7 and beyond are unknown *)
	
		  
    (* TWO BANDS TURING MACHINES *)

    let (generic_copy: symbols -> turing_machine) = fun symbols ->
	  let init = nop.initial and accept = nop.accept in
	    let q = State.fresh_from init in	          	  
	      let generic_transitions =
		Transition.foreach_symbol_of symbols (BUT B)
		  (fun s ->
			[ (init, Action( Simultaneous [ RWM(Match(VAL s), No_Write, Right) ; RWM(Match ANY, Write s, Right) ]), init) ]
		  )
	      in 
		{ nop with
		  nb_bands = 2 ;
		  name = "copy_" ^ (Pretty.set Symbol.to_ascii symbols) ;
		  transitions = generic_transitions
		  @ [ (init, Action( Simultaneous [ RWM(Match(VAL B), No_Write, Left)  ; RWM(Match ANY, No_Write, Left) ]), Q 100) ;
		      (Q 100, Parallel [ Run(left_most) ; Run (left_most)], accept) 
		    ] 
		}


     let (generic_copy_with_4: symbols -> turing_machine) = fun symbols ->
	  let init = nop.initial and accept = nop.accept in
	    let q = State.fresh_from init in	          	  
	      let generic_transitions =
		Transition.foreach_symbol_of symbols (BUT B)
		  (fun s ->
			[ (init, Action( Simultaneous [ RWM(Match ANY, No_Write, Here);RWM(Match ANY, No_Write, Here);RWM(Match(VAL s), No_Write, Right) ; RWM(Match ANY, Write s, Right) ]), init) ]
		  )
	      in 
		{ nop with
		  nb_bands = 4 ;
		  name = "copy_4" ^ (Pretty.set Symbol.to_ascii symbols) ;
		  transitions = generic_transitions
		  @ [ (init, Action( Simultaneous [ RWM(Match ANY, No_Write, Here);RWM(Match ANY, No_Write, Here);RWM(Match(VAL B), No_Write, Left)  ; RWM(Match ANY, No_Write, Left) ]), Q 100) ;
		      (Q 100, Parallel [ Run(nop);Run(nop);Run(left_most) ; Run (left_most)], accept) 
		    ] 
		}

   let (copy_1_on_4: symbols -> turing_machine) = fun symbols ->
	  let init = nop.initial and accept = nop.accept in
	    let q = State.fresh_from init in	          	  
	      let generic_transitions =
		Transition.foreach_symbol_of symbols (BUT B)
		  (fun s ->
			[ (init, Action( Simultaneous [ RWM(Match (VAL s), No_Write, Right);RWM(Match (ANY), No_Write, Here);RWM(Match(ANY), No_Write, Here) ; RWM(Match (ANY), Write s, Right) ]), init) ]
		  )
	      in 
		{ nop with
		  nb_bands = 4 ;
		  name = "copy_14" ^ (Pretty.set Symbol.to_ascii symbols) ;
		  transitions = generic_transitions
		  @ [ (init, Action( Simultaneous [ RWM(Match (VAL B), No_Write, Here);RWM(Match ANY, No_Write, Here);RWM(Match(ANY), No_Write, Here)  ; RWM(Match ANY, No_Write, Here) ]), Q 100) ;
		      (Q 100, Parallel [ Run(nop);Run(nop);Run(nop) ; Run (left_most)], accept) 
		    ] 
		}
   let (copy_4_on_1: symbols -> turing_machine) = fun symbols ->
	  let init = nop.initial and accept = nop.accept in
	    let q = State.fresh_from init in	          	  
	      let generic_transitions =
		Transition.foreach_symbol_of symbols (BUT B)
		  (fun s ->
			[ (init, Action( Simultaneous [ RWM(Match (ANY), Write s, Right);RWM(Match (ANY), No_Write, Here);RWM(Match(ANY), No_Write, Here) ; RWM(Match (VAL s), No_Write, Right) ]), init) ]
		  )
	      in 
		{ nop with
		  nb_bands = 4 ;
		  name = "copy_41" ^ (Pretty.set Symbol.to_ascii symbols) ;
		  transitions = generic_transitions
		  @ [ (init, Action( Simultaneous [ RWM(Match (ANY), No_Write, Here);RWM(Match ANY, No_Write, Here);RWM(Match(ANY), No_Write, Here)  ; RWM(Match (VAL B), No_Write, Here) ]), Q 100) ;
		      (Q 100, Parallel [ Run(nop);Run(nop);Run(nop) ; Run (left_most)], accept) 
		    ] 
		}
	
    let (generic_reverse: symbols -> turing_machine) = fun symbols ->
	  let init = nop.initial and accept = nop.accept in
	    let copy = State.fresh_from init in
	      let head = State.fresh_from copy in
		let	generic_transitions = Transition.foreach_symbol_of symbols (BUT B)
		    (fun s ->
			  [ (copy, Action( Simultaneous [ RWM (Match(VAL s), No_Write, Left) ; RWM (Match ANY, Write s, Right) ]), copy) ]
		    )
		in 
		  { nop with
		    nb_bands = 2 ;
		    name = "rev_" ^ (Pretty.set Symbol.to_ascii symbols) ;
		    transitions = generic_transitions
		    @ [ (init, Parallel [ Run(right_most) ; Action(Nop) ], copy) ;			
			(copy, Parallel [ Action( RWM (Match(VAL B), No_Write, Right)) ; Action( RWM (Match(VAL B), No_Write, Left)) ], head) ;
			(head, Parallel [ Action(Nop) ; Run(left_most) ], accept)
		      ] 
		  }	
		    
    let (xor:turing_machine) = 
      let init = nop.initial and accept = nop.accept in
	let q = State.fresh_from init in	          	  
	  { nop with
	    nb_bands = 2 ;
	    name = "xor" ;
	    transitions =
	    [
	     (init, Action( Simultaneous [ RWM (Match(VAL Z), Write Z, Right) ; RWM (Match(VAL Z), No_Write, Right) ]), init) ;
	     (init, Action( Simultaneous [ RWM (Match(VAL Z), Write U, Right) ; RWM (Match(VAL U), No_Write, Right) ]), init) ;
	     (init, Action( Simultaneous [ RWM (Match(VAL U), Write Z, Right) ; RWM (Match(VAL U), No_Write, Right) ]), init) ;
	     (init, Action( Simultaneous [ RWM (Match(VAL U), Write U, Right) ; RWM (Match(VAL Z), No_Write, Right) ]), init) ;
	     (init, Action( Simultaneous [ RWM (Match(VAL B), No_Write, Left) ; Nop ]), q) ;
	     (q, Parallel [ Run(left_most) ; Run(left_most) ], accept) 
	   ]
	  }

	(*Marche*)
	let(check_parenthesis :turing_machine) = 
		let init = nop.initial and accept = nop.accept and reject = nop.reject in
			let q = State.fresh_from init and state_1 = State.fresh_from init and state_2 = State.fresh_from init  in{
				nop with
				nb_bands = 2;
				name = "cp";
				transitions =
				[	
					(* Match (OUT [O;B;P]) Pour avoir plusieurs valeurs exclues*)
					(init, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ]), state_1);
					(init, Action( Simultaneous [ RWM (Match(VAL B), No_Write , Here) ; RWM (Match(VAL B), No_Write, Here) ]), accept);
					(init, Action( Simultaneous [ RWM (Match(VAL B), No_Write , Here) ; RWM (Match(VAL O), No_Write, Here) ]), reject);
					(init, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Here) ; RWM (Match(VAL B), No_Write, Here) ]), reject);
					(init, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Right) ; RWM (Match(VAL O), Write B, Left) ]), init);
					(init, Action( Simultaneous [ RWM (Match (OUT [O;B;C]), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ]), init);
					(state_1, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(BUT B), No_Write, Right) ]), state_2);
					(state_2, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL B), Write O, Here) ]), init);

				]
	}



let(real_one :turing_machine) = 
		let init = nop.initial and accept = nop.accept and reject = nop.reject in
			let q = State.fresh_from init in{
				nop with
				nb_bands = 3;
				name = "real_one";
				transitions =
				[	
					(* Match (OUT [O;B;P]) Pour avoir plusieurs valeurs exclues*)

					(*Si parethèse ouvrante : l'empiler.*)
					(init, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(VAL B), Write O, Right) ; RWM (Match(VAL B), Write O, Right)]), init);

					(*Si terme quelconque : l'écrire sur la bande.*)
					(init, Action( Simultaneous [ RWM (Match(VAL L), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write L, Right)]), init);
					(init, Action( Simultaneous [ RWM (Match(VAL D), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write D, Right)]), init);
					(init, Action( Simultaneous [ RWM (Match(VAL U), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write U, Right)]), init);
					(init, Action( Simultaneous [ RWM (Match(VAL Z), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write Z, Right)]), init);
					(init, Action( Simultaneous [ RWM (Match(VAL X), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write X, Right)]), init);
					(*Si parenthèse fermante : *)
					(init, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Right) ; RWM (Match(VAL B), No_Write, Left) ; RWM (Match(VAL B), Write C, Right)]), Q 2);

					(*On la dépile *)
					(Q 2, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), Write B, Left) ; RWM (Match(ANY), No_Write, Here)]), Q 3);

					(*Si c'est la derniere : accepter*)
					(Q 3, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL B), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), accept);

					(*Sinon retourner dans l'état initial*)
					(Q 3, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), No_Write, Right) ; RWM (Match(ANY), No_Write, Here)]), init);
				
				]
	}


let(copyTerme : symbols -> turing_machine) = fun symbols ->
		let init = nop.initial and accept = nop.accept and reject = nop.reject in
			let q = State.fresh_from init in
				let	generic_transitions = Transition.foreach_symbol_of symbols (OUT [O;B;C])
		    		(fun s ->
				  [ (Q 4, Action( Simultaneous [ RWM (Match(VAL s), Write S , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write s, Right)]), Q 4)]
		   		 )in
				{
				nop with
				nb_bands = 3;
				name = "application"^ (Pretty.set Symbol.to_ascii symbols) ;
				transitions = generic_transitions
				@ [	
					(* Match (OUT [O;B;P]) Pour avoir plusieurs valeurs exclues*)

					(*Oublier le premier terme*)
					(*Si parethèse ouvrante : l'empiler.*)
					(init, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(VAL B), Write O, Right) ; RWM (Match(ANY), No_Write, Here)]), init);

					(*Si terme quelconque : Oublier.*)
					(init, Action( Simultaneous [ RWM (Match(OUT[O;C;B]), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), init);
					(init, Action( Simultaneous [ RWM (Match(VAL B), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Right)]), reject);
					

					(*Si parenthèse fermante : *)
					(init, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Right) ; RWM (Match(VAL B), No_Write, Left) ; RWM (Match(ANY), No_Write, Here)]), Q 2);

					(*On la dépile *)
					(Q 2, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), Write B, Left) ; RWM (Match(ANY), No_Write, Here)]), Q 3);

					(*Si c'est la derniere : passer au terme a copier sur la bande suivante*)
					(Q 3, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL B), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 4);

					(*Sinon retourner dans l'état initial*)
					(Q 3, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), No_Write, Right) ; RWM (Match(ANY), No_Write, Here)]), init);

					(*A partir de là, on est sur le terme a recopier.*)
					(*Empiler les parenthèses ouvrantes.*)
					(Q 4, Action( Simultaneous [ RWM (Match(VAL O), Write S , Right) ; RWM (Match(VAL B), Write O, Right) ; RWM (Match(VAL B), Write O, Right)]), Q 4);
					
					(*Empiler ecrire les termes*)
					(Q 4, Action( Simultaneous [ RWM (Match(VAL B), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Right)]), reject);

					(*Si parenthèse fermante : *)
					(Q 4 , Action( Simultaneous [ RWM (Match(VAL C), Write S , Right) ; RWM (Match(VAL B), No_Write, Left) ; RWM (Match(VAL B), Write C, Right)]), Q 5);

					(*On la dépile *)
					(Q 5, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), Write B, Left) ; RWM (Match(ANY), No_Write, Here)]), Q 6);

					(*Si c'est la derniere : accepter*)
					(Q 6, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL B), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), accept);

					(*Sinon retourner dans l'état initial*)
					(Q 6, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), No_Write, Right) ; RWM (Match(ANY), No_Write, Here)]), Q 4);
				
				]
	}
(* Application pas générique du tout !
let(application :turing_machine) = 
		let init = nop.initial and accept = nop.accept and reject = nop.reject in
			let q = State.fresh_from init in{
				nop with
				nb_bands = 3;
				name = "application";
				transitions =
				[	
					(* Match (OUT [O;B;P]) Pour avoir plusieurs valeurs exclues*)

					(*Oublier le premier terme*)
					(*Si parethèse ouvrante : l'empiler.*)
					(init, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(VAL B), Write O, Right) ; RWM (Match(ANY), No_Write, Here)]), init);

					(*Si terme quelconque : Oublier.*)
					(init, Action( Simultaneous [ RWM (Match(OUT[O;C;B]), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), init);
					(init, Action( Simultaneous [ RWM (Match(VAL B), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Right)]), reject);
					

					(*Si parenthèse fermante : *)
					(init, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Right) ; RWM (Match(VAL B), No_Write, Left) ; RWM (Match(ANY), No_Write, Here)]), Q 2);

					(*On la dépile *)
					(Q 2, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), Write B, Left) ; RWM (Match(ANY), No_Write, Here)]), Q 3);

					(*Si c'est la derniere : passer au terme a copier sur la bande suivante*)
					(Q 3, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL B), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 4);

					(*Sinon retourner dans l'état initial*)
					(Q 3, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), No_Write, Right) ; RWM (Match(ANY), No_Write, Here)]), init);

					(*A partir de là, on est sur le terme a recopier.*)
					(*Empiler les parenthèses ouvrantes.*)
					(Q 4, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(VAL B), Write O, Right) ; RWM (Match(VAL B), Write O, Right)]), Q 4);
					
					(*Empiler ecrire les termes*)
					(Q 4, Action( Simultaneous [ RWM (Match(VAL L), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write L, Right)]), Q 4);
					(Q 4, Action( Simultaneous [ RWM (Match(VAL D), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write D, Right)]), Q 4);
					(Q 4, Action( Simultaneous [ RWM (Match(VAL U), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write U, Right)]), Q 4);
					(Q 4, Action( Simultaneous [ RWM (Match(VAL Z), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write Z, Right)]), Q 4);
					(Q 4, Action( Simultaneous [ RWM (Match(VAL X), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL B), Write X, Right)]), Q 4);
					(Q 4, Action( Simultaneous [ RWM (Match(VAL B), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Right)]), reject);

					(*Si parenthèse fermante : *)
					(Q 4 , Action( Simultaneous [ RWM (Match(VAL C), No_Write , Right) ; RWM (Match(VAL B), No_Write, Left) ; RWM (Match(VAL B), Write C, Right)]), Q 5);

					(*On la dépile *)
					(Q 5, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), Write B, Left) ; RWM (Match(ANY), No_Write, Here)]), Q 6);

					(*Si c'est la derniere : accepter*)
					(Q 6, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL B), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), accept);

					(*Sinon retourner dans l'état initial*)
					(Q 6, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL O), No_Write, Right) ; RWM (Match(ANY), No_Write, Here)]), Q 4);
				
				]
	}
*)
let(substitution :symbols -> turing_machine) = fun symbols ->
		let init = nop.initial and accept = nop.accept and reject = nop.reject in
			let q = State.fresh_from init in
			let	generic_transitions = Transition.foreach_symbol_of symbols (OUT [O;C])
		    		(fun s ->
				  [ 	(*Ecrire les X,U et Z de la variable.*)
					(Q 4, Action( Simultaneous [ RWM (Match(VAL s),  No_Write , Right) ; RWM (Match(ANY), Write s, Right) ; RWM (Match(ANY), No_Write, Here); RWM (Match(ANY), No_Write, Here)]), Q 4);
					(*Ecrire les X, U et Z du lambda*)
					(Q 31, Action( Simultaneous [ RWM (Match(VAL s),  No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here); RWM (Match(ANY), Write s, Right)]), Q 31)]
		   		 )in
			let	generic_transitions_2 = Transition.foreach_symbol_of symbols (OUT [S;X;U;Z;L])
		    		(fun s ->
					(*Ecrire les parentheses sur la quatrième bande*)
				 	 [ (Q 30, Action( Simultaneous [ RWM (Match(VAL s), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here); RWM (Match(ANY), Write s, Right)]), Q 30)]
		   		 )in
			let	check_equality = Transition.foreach_symbol_of symbols (IN[Z;U])
		    		(fun s ->
					
				 	 [ 
					
					]
		   		 )in						
				{
				nop with
				nb_bands = 4;
				name = "substitutionDemo" ; 
				transitions = generic_transitions @ generic_transitions_2 @ check_equality
				@ [	
					(* Ok ! on commence : On place le terme a substituer sur la troisième bande *)
					(init,  Run(copyTerme symbols) ,  Q 2);
					(*On ramene la premiere bande a gauche, idem pour la troisieme.*)
					(Q 2 , Parallel [ Run(left_most) ; Run(nop);Run(left_most);Run(nop)], Q 3);
					(*Ok ! A partir de là, on a le terme a substituer sur la troisième bande et on est au debut de la bande 1 et 3.*)
					(* Sauter la toute parenthèse ouvrante : *)
					(Q 3, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write,Here)]), Q 3);
					(*On tombe sur le premier Lambda : le recopier sur la bande 2 pour savoir quelle variable sera a substituer.*)
					(Q 3, Action( Simultaneous [ RWM (Match(VAL L),  No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write,Here)]), Q 4 );
					(*Si il n'y a pas de lambda asssocie a notre application : une erreur est survenue*)
					(Q 3, Action( Simultaneous [ RWM (Match(OUT[O;L]),  No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write,Here)]), reject);
						
					(*Si en recopiant un lambda on tombe sur une parenthèse fermante, alors erreur. *)
						(Q 4, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), reject);
					(*Si on a une parenthèse ouvrante, revenir à l'état où on cherche.*)
						(Q 4, Action( Simultaneous [ RWM (Match(VAL O),  No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write O, Right)]), Q 30);

					(*A partir de là, le nom de la variable a substituer est sur la bande 2.*)
					(*Si on a une variable, alors il faut la remplacer : recopier sur la bande 4 la bande 3.*)
					(Q 30, Action( Simultaneous [ RWM (Match(VAL X),  No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write X, Right)]), Q 70);				(*Placer la bande de la variable après le X.*)
						(Q 70, Parallel[Run(nop);Run(left_most);Run(nop);Run(nop)], Q 80);
						(Q 80, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(ANY), No_Write, Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 81);

						(*Puis checker l'égalité.*)
						(*Si on a égalité stricte.*)
						(Q 81, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(VAL B), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 82);
						(*effacer la bande 4 jusqu'a la variable X*)
						(Q 82, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(BUT X), Write B, Left)]), Q 81);
						(Q 82, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(VAL X), Write B, Here)]), Q 85);
						(*Avancer dans l'égalité.*)
						(Q 81, Action( Simultaneous [ RWM (Match(VAL Z), No_Write , Right) ; RWM (Match(VAL Z), No_Write, Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write Z, Right)]), Q 81);
						(Q 81, Action( Simultaneous [ RWM (Match(VAL U), No_Write , Right) ; RWM (Match(VAL U), No_Write, Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write U, Right)]), Q 81);
						(*Sinon quitter quand on détecte une différence qui sont autant de chances.*)
						(Q 81, Action( Simultaneous [ RWM (Match(VAL U), No_Write , Right) ; RWM (Match(VAL Z), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write U, Right)]), Q 30);
						(Q 81, Action( Simultaneous [ RWM (Match(VAL Z), No_Write , Right) ; RWM (Match(VAL U), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write Z, Right)]), Q 30);

						(*Debut de la recopie si on a égalité stricte*)
						(Q 85, Parallel[Run(nop);Run(nop);Run(nop);Run(nop)], Q 90);
						(Q 90, Run(generic_copy_with_4 symbols), Q 100);
						(Q 100, Parallel[Run(nop);Run(nop);Run(nop);Run(goto_right_blank)], Q 30);
					
					(*Si on a un dollar : terminer.*)
					(Q 30, Action( Simultaneous [ RWM (Match(VAL S), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 320 );
						(*Supprimer la derniere parenthese fermante.*)
						(Q 320, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Left)]), Q 321 );
						(Q 321, Action( Simultaneous [ RWM (Match(ANY), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write B, Here)]), Q 32 );

						(*Passer les dollars*)
						(Q 32, Action( Simultaneous [ RWM (Match(VAL S), No_Write, Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 32);			(*Si y'en a pas alors plus de beta réductions a faire : accepter.*)
						(Q 32, Action( Simultaneous [ RWM (Match(VAL B), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), accept);
						(*Si il en reste, alors recopier les beta réductions restantes sur la bande 4*)
						(Q 32, Action( Simultaneous [ RWM (Match(OUT[S;B]), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 33);
						(*Recopie*)
						(Q 33 , Run(copy_1_on_4 symbols),Q 34);
						(*On met toutes les bandes à gauche.*)
						(Q 34 , Parallel[Run(left_most);Run(left_most);Run(left_most);Run(left_most)],Q 35);
						(*Effacer les 3 premieres bandes.*)
						(Q 35 , Parallel[Run(erase);Run(erase);Run(erase);Run(nop)],Q 36);
						(*Recopié le terme substitué sur la bande 1.*)
						(Q 36 , Run(copy_4_on_1 symbols),Q 37);
						(*Revenir a gauche de la première bande et itérer.*)
						(Q 37 , Parallel[Run(left_most);Run(nop);Run(nop);Run(erase)],init);
					
					
					
					(*Si on a un 1 ou un 0 les recopier (dans le cas ou on a détecté une inégalité)*)
					(Q 30, Action( Simultaneous [ RWM (Match(VAL U), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY),Write U ,Right)]), Q 30);
					(Q 30, Action( Simultaneous [ RWM (Match(VAL Z), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write Z,Right)]), Q 30);
					(*Si on a un lambda, recopier la suite*)
					(Q 30, Action( Simultaneous [ RWM (Match(VAL L),  No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write L, Right)]), Q 31);
						(*Si on a une fermante : recopier*)
						(Q 31, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), reject);
						(*Si on a une parenthèse ouvrante, revenir à l'état où on cherche les variables.*)
						(Q 31, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write O, Right)]), Q 30);
					
				]
	}

(*Prendre celle-là pour la démo si celle d'en haut ne marche pas du tout.
let(substitution :symbols -> turing_machine) = fun symbols ->
		let init = nop.initial and accept = nop.accept and reject = nop.reject in
			let q = State.fresh_from init in
			let	generic_transitions = Transition.foreach_symbol_of symbols (OUT [O;C])
		    		(fun s ->
				  [ 	(*Ecrire les X,U et Z de la variable.*)
					(Q 4, Action( Simultaneous [ RWM (Match(VAL s), No_Write , Right) ; RWM (Match(ANY), Write s, Right) ; RWM (Match(ANY), No_Write, Here); RWM (Match(ANY), No_Write, Here)]), Q 4);
					(*Ecrire les X, U et Z du lambda*)
					(Q 31, Action( Simultaneous [ RWM (Match(VAL s), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here); RWM (Match(ANY), Write s, Right)]), Q 31)]
		   		 )in
			let	generic_transitions_2 = Transition.foreach_symbol_of symbols (OUT [S;X;U;Z;L])
		    		(fun s ->
					(*Ecrire sur la quatrième bande*)
				 	 [ (Q 30, Action( Simultaneous [ RWM (Match(VAL s), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here); RWM (Match(ANY), Write s, Right)]), Q 30)]
		   		 )in					
				{
				nop with
				nb_bands = 4;
				name = "substitution"^ (Pretty.set Symbol.to_ascii symbols) ; 
				transitions = generic_transitions @ generic_transitions_2
				@ [	
					(* Ok ! on commence : On place le terme a substituer sur la troisième bande *)
					(init,  Run(application symbols) ,  Q 2);
					(Q 2 , Parallel [ Run(left_most) ; Run(nop);Run(left_most);Run(nop)], Q 3);
					(*Ok ! A partir de là, on a le terme a substituer sur la troisième bande et on est au debut de la bande 1 et 3.*)
					(* Sauter la parenthèse ouvrante : *)
					(Q 3, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write O,Here)]), Q 3);
					(*On tombe sur le premier Lambda terme : le recopier sur la bande 2.*)
					(Q 3, Action( Simultaneous [ RWM (Match(VAL L), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write,Here)]), Q 4 );
						
					(*Si en passant un Lambda terme on tombe sur une parenthèse fermante, alors pas valide. *)
						(Q 4, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), reject);
					(*Si on a une parenthèse ouvrante, revenir à l'état où on cherche.*)
						(Q 4, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(ANY), No_Write, Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write O, Right)]), Q 30);

					(*A partir de là, la variable a substituer est sur la bande 2*)

					(*Si on a une variable, alors il faut la remplacer : recopier sur la bande 4 la bande 3*)
					(Q 30, Action( Simultaneous [ RWM (Match(VAL X), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 70);
						(Q 70, Parallel[Run(nop);Run(left_most);Run(nop);Run(nop)], Q 80);
						(Q 80, Parallel[Run(nop);Run(nop);Run(nop);Run(goto_right_blank)], Q 90);
						(Q 90, Run(generic_copy_with_4 symbols), Q 100);
						(Q 100, Parallel[Run(nop);Run(nop);Run(nop);Run(goto_right_blank)], Q 30);
					
					(*Si on a un dollar : terminer.*)
					(Q 30, Action( Simultaneous [ RWM (Match(VAL S), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Left)]), Q 32 );
					(Q 32, Action( Simultaneous [ RWM (Match( ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write B, Here)]), accept );
					
					(*Si on a un 1 ou un 0 inopiné, ne pas les marquer.*)
					(Q 30, Action( Simultaneous [ RWM (Match(IN[U;Z]), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 30);
					(*Si on a un lambda, recopier la suite*)
					(Q 30, Action( Simultaneous [ RWM (Match(VAL L), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write L, Right)]), Q 31);
						(*Si on a une fermante : erreur*)
						(Q 31, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), reject);
						(*Si on a une parenthèse ouvrante, revenir à l'état où on cherche les variables.*)
						(Q 31, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(ANY), No_Write, Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write O, Right)]), Q 30);
					
				]
	}
*)



(*	Obsolète
let(substitution :symbols -> turing_machine) = fun symbols ->
		let init = nop.initial and accept = nop.accept and reject = nop.reject in
			let q = State.fresh_from init in
			let	generic_transitions = Transition.foreach_symbol_of symbols (OUT [O;C])
		    		(fun s ->
				  [ (Q 4, Action( Simultaneous [ RWM (Match(VAL s), No_Write , Right) ; RWM (Match(ANY), Write s, Right) ; RWM (Match(ANY), No_Write, Here); RWM (Match(ANY), No_Write, Here)]), Q 4)]
		   		 )in{
				nop with
				nb_bands = 4;
				name = "substitution"^ (Pretty.set Symbol.to_ascii symbols) ; 
				transitions = generic_transitions
				@ [	
					(* Ok ! on commence : On place le terme a substituer sur la troisième bande *)
					(init,  Run(application symbols) ,  Q 2);
					(Q 2 , Parallel [ Run(left_most) ; Run(nop);Run(left_most);Run(nop)], Q 3);
					(*Ok ! A partir de là, on a le terme a substituer sur la troisième bande et on est au debut de la bande 1 et 3.*)
					(Q 3, Action( Simultaneous [ RWM (Match(OUT[L;X;O;C;S]), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 3 );
					(*Si on tombe sur un Lambda terme : le recopier sur la bande 2.*)
					(Q 3, Action( Simultaneous [ RWM (Match(VAL L), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write,Here)]), Q 4 );
						(*Ecrire la variable sur la bande 2*)
						
					(*Si en passant un Lamba terme on tombe sur une parenthèse fermante, alors pas valide. *)
						(Q 4, Action( Simultaneous [ RWM (Match(VAL C), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), reject);
					(*Si on a une parenthèse ouvrante, revenir à l'état où on cherche.*)
						(Q 4, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(ANY), No_Write, Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write O, Right)]), Q 3);




					(*Si on a une variable, alors il faut la remplacer : recopier sur la bande 4 la bande 3*)
					(Q 3, Action( Simultaneous [ RWM (Match(VAL X), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), Q 7);
						(Q 7, Parallel[Run(nop);Run(nop);Run(nop);Run(goto_right_blank)], Q 8);
						(Q 8, Run(generic_copy_with_4 symbols), Q 9);
						(Q 9, Parallel[Run(nop);Run(nop);Run(nop);Run(goto_right_blank)], Q 3);
					

					(*Si on a une parenthèse fermante.*)
					(Q 3 , Action( Simultaneous [ RWM (Match(VAL C), No_Write , Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write C, Right)]), Q 3);
					(*Si on a un dollar.*)
					(Q 3, Action( Simultaneous [ RWM (Match(VAL S), No_Write , Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), No_Write, Here)]), accept);
						
					(* Si on a une parenthèse ouvrante : *)
					(Q 3, Action( Simultaneous [ RWM (Match(VAL O), No_Write , Right) ; RWM (Match(ANY), No_Write, Right) ; RWM (Match(ANY), No_Write, Here) ; RWM (Match(ANY), Write O,Right)]), Q 3);
					
					
				]
	} *)
	    
  end)

    

(* Micha�l P�RIN, Verimag / Universit� Grenoble-Alpes, F�vrier 2017
 *
 * Part of the project TURING MACHINES FOR REAL
 *
 * (PROJECT 2019)  1. Multi-Bands Turing Machines working on a an alphabet A can be simulated by a single band Turing Machine using a augmented Alphbet A'
 *
 * (PROJECT 2017)  2. A Turing Machine using an alphabet A can be simulated by a Turing Machine using the binary alphabet {B,D}
 *
 * This module provides means to write Emulator for Problems 1 and 2.
 *
 *)



open Tricks
open State
open Action
open Transition
open Band
open Configuration
open Turing_Machine
open Execution
open Alphabet



type emulator   = State.t * Action.t * State.t -> Turing_Machine.t
type translator = Band.t list -> Band.t list

type simulator  =
    { name: string ;
      encoder: translator ;
      decoder: translator ;
      emulator: emulator
    }

type simulators = simulator list


module Simulator =
  (struct

    type loggers = Logger.t list

    let (fake_tm_named: string ->  Turing_Machine.t) = fun name ->
	  Turing_Machine.finalize name Turing_Machine.nop

    let (show_bands_using: loggers -> string -> Band.t list -> Band.t list) = fun loggers name bands ->
	  begin
 	    (Configuration.make (fake_tm_named name) bands) >> (Configuration.print_using loggers) ;
	    bands
	  end

    let rec (execute_action_using: simulators * loggers -> (State.t * Action.t * State.t) -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (src,action,tgt) cfg ->
	  let cfg = cfg >> (Configuration.show_using loggers)
	  in
    let next_bands =
      match simulators with
      | [] -> Action.perform action cfg.bands

      | simulator :: other_simulators
        ->
        let e_tm    = simulator.emulator (src,action,tgt)
        and e_bands = (simulator.encoder  cfg.bands) >> (show_bands_using loggers (String.concat " to " [ "encoding" ; simulator.name ]))
        in
        let e_cfg = Configuration.make e_tm e_bands
        in
        let e_next_cfg = log_run_using (other_simulators,loggers) e_cfg
        in
	    let bands_updated_by_emulation = (simulator.decoder e_next_cfg.bands) >> (show_bands_using loggers (String.concat " " [ simulator.name ; "decoding"]))
	    in
        let bands_updated_by_execution = Action.perform action cfg.bands
        in
        let equivalent = List.map2(fun bandExecution bandEmulation -> Band.equivalent bandExecution bandEmulation) bands_updated_by_execution bands_updated_by_emulation
        in
        let rec allTrue = fun bool_List ->
            match bool_List with
            | [] -> true
            | h::t -> if h then allTrue t else h
        in
        if allTrue equivalent
			  then bands_updated_by_execution
			  else failwith
				  (String.concat " \n " [ "execute_action_using: simulation errors" ;
							Band.to_ascii_many bands_updated_by_emulation ;
							"are not equivalent to" ;
							Band.to_ascii_many bands_updated_by_execution ;
						      ])
	    in
      { cfg with bands = next_bands }


    and (execute_single_band_instruction_using: simulators * loggers -> (State.t * Instruction.t * State.t) -> Band.t -> Band.t) = fun (simulators,loggers) (src,instruction,tgt) band ->
	  let cfg = Configuration.make (fake_tm_named (Instruction.pretty instruction)) [band]
	  in let next_cfg = execute_instruction_using (simulators,loggers) (src,instruction,tgt) cfg
	  in List.hd next_cfg.bands

    and (execute_instruction_using: simulators * loggers -> (State.t * Instruction.t * State.t) -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (source,instruction,target) cfg ->
	  (match instruction with
	  | Run tm -> (* FIXME: ajoutez les transitions (source -nop-> init) et (accept -nop-> target) *)
		  run_using (simulators,loggers) (Configuration.make tm cfg.bands)

	  | Seq [] -> cfg
	  | Seq (inst::instructions) ->
		  let intermediate_state = State.fresh_from source in
		    cfg
		      >> (execute_instruction_using (simulators,loggers) (source, inst, intermediate_state))
		      >> (execute_instruction_using (simulators,loggers) (intermediate_state, Seq instructions, target))

	  | Parallel instructions ->
		  let next_bands =
		    List.map
		      (fun (inst,band) -> execute_single_band_instruction_using (simulators,loggers) (source,inst,target) band)
		      (Instruction.zip instructions cfg.bands)
		  in { cfg with bands = next_bands }

	  | Action action -> execute_action_using (simulators,loggers) (source,action,target) cfg
	  )

    and (execute_transition_using: simulators * loggers -> Transition.t -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (source,instruction,target) cfg ->
	  let next_cfg = execute_instruction_using (simulators,loggers) (source,instruction,target) cfg
	  in { next_cfg with state = target}

    and (run_using: simulators * loggers -> Configuration.t -> Configuration.t) = fun (simulators,loggers) cfg ->
	  match Execution.select_enabled_transition cfg.tm cfg with
	  | None -> cfg
	  | Some transition ->
		  let next_cfg = execute_transition_using (simulators,loggers) transition cfg
		  in run_using (simulators,loggers) next_cfg

    and (log_run_using: simulators * loggers -> Configuration.t -> Configuration.t) = fun (simulators,loggers) cfg ->
	  let loggers = cfg.logger :: loggers
	  in
	    let final_cfg = (run_using (simulators,loggers) cfg) >> (Configuration.show_using loggers)
	    in
	      begin
		cfg.logger#close ;
		final_cfg
	      end

  end)


open State
open Symbol
open Pattern
open Action
open Band
open Transition
open Turing_Machine

(* An example of a useless but correct translation that splits the effect of a transition into three steps

   (q) -- l / e : d --> (q')
   ===
   (q) -- l : H --> (q.0) -- ANY / e : H --> (q.00) -- ANY : d --> (q')
*)


module Split =
  (struct

    (* TRANSLATION OF BANDS *)

    let (encode: translator) = fun x -> x

    (* REVERSE TRANSLATION *)

    let (decode: translator) = fun x -> x

    (* EMULATION OF TRANSITIONS *)

    let (just_read: reading -> Action.t) = fun reading ->
	  RWM (reading, No_Write, Here)

    let (just_write: writing -> Action.t) = fun writing ->
	  match writing with
	  | No_Write     -> Nop
	  | Write symbol -> RWM (Match(ANY), Write symbol, Here)

    let (just_move: moving -> Action.t) = fun moving ->
	  RWM (Match(ANY), No_Write, moving)

    let (synchronize: Action.t list -> Instruction.t) = fun actionS ->
	  let rec (rec_synchronize: ('r list * 'w list * 'm list) -> Action.t list -> ('r list * 'w list * 'm list)) = fun (reads,writes,moves) actions ->
		match actions with
		| [] -> (List.rev reads, List.rev writes, List.rev moves)
		| action::actions ->
			(match action with
			| Nop        -> rec_synchronize ( Nop::reads , Nop::writes , Nop::moves) actions
			| RWM(r,w,m) -> rec_synchronize ( (just_read r)::reads , (just_write w)::writes , (just_move m)::moves) actions
			| Simultaneous _ -> failwith "Emulator.Split.synchronize: nested Simultaneous"
			)
	  in
	    let (reads,writes,moves) = rec_synchronize ([],[],[]) actionS
	    in
	      Seq[ Action(Simultaneous(reads)) ; Action(Simultaneous(writes)) ; Action(Simultaneous(moves)) ]

    let rec (transitions_emulating: State.t * Action.t * State.t -> Transition.t list) = fun (source,action,target) ->
	    (match action with
	    | Nop -> [ (source, Action(Nop), target) ]

	    | RWM(r,w,m) -> [ (source, Seq[ Action(just_read r) ; Action(just_write w) ; Action(just_move m) ], target) ]

	    | Simultaneous actions -> [ (source, synchronize actions, target) ]
	    )

    and (emulate_action: emulator) = fun (source,action,target) ->
	  let (source,target) =
	    if source <> target   (* /!\ loop in the emulated TM if source-target *)
	    then (source,target)
	    else (State.initial, State.accept)
	  in
	    let transitions =  transitions_emulating (source,action,target) in
	      { Turing_Machine.nop with
		name = String.concat "" [ "Split" ; Pretty.parentheses (Transition.to_ascii (source,Action action, target)) ] ;
		initial = source ;
		accept  = target ;
		transitions = transitions
	      }

    (* THE SIMULATOR *)

    let (* USER *) (simulator: simulator) = { name = "Split" ; encoder = encode ;  decoder = decode ; emulator = emulate_action }

  end)



  module MiseAuPoint =
    (struct

    let change_Symbol symbol =
        match symbol with
        | Z -> D
        | U -> S
        | _ -> symbol

    let rec change_Symbols lst_Source lst_Target =
        match lst_Source with
        | [] -> lst_Target
        | h :: t -> change_Symbols t ((change_Symbol h)::lst_Target)


      (* TRANSLATION OF BANDS *)

      let (encode_on_one_band: Band.t -> Band.t) = fun band ->

        let left = change_Symbols band.left [] in
        let right = List.rev (change_Symbols band.right []) in
        let head = change_Symbol band.head in
        {
            empty with
            left = left ;
            head = head ;
            right = right ;
            alphabet = Alphabet.make [B;D;S];
        }

      let encode: Band.t list -> Band.t list = fun bands ->
        List.map(fun band -> encode_on_one_band band) bands


      (* REVERSE TRANSLATION *)

      let (decode_on_one_band: Band.t -> Band.t) = fun band ->

        let change_Symbol_decode symbol =
            match symbol with
            | D -> Z
            | S -> U
            | _ -> symbol
        in
        let rec change_Symbols_decode lst_Source lst_Target =
            match lst_Source with
            | [] -> lst_Target
            | h :: t -> change_Symbols_decode t ((change_Symbol_decode h)::lst_Target)
        in

        let left = change_Symbols_decode band.left [] in
        let right = List.rev (change_Symbols_decode band.right []) in
        let head = change_Symbol_decode band.head in
        {
            empty with
            left = left ;
            head = head ;
            right = right ;
            alphabet = Alphabet.make [B;D;S];
        }


        let decode: Band.t list -> Band.t list = fun bands ->
            List.map(fun band -> decode_on_one_band band) bands


      (* EMULATION OF TRANSITIONS *)

      let (change_Read: reading -> reading) = fun reading ->

          match reading with
              | Match pattern -> 	  match pattern with
                                  	  | ANY -> Match(ANY)
                                  	  | VAL a -> Match(VAL (change_Symbol a))
                                  	  | BUT a -> Match(BUT (change_Symbol a))
                                  	  | IN  aS -> Match(IN (change_Symbols aS []))
                                  	  | OUT aS -> Match(OUT (change_Symbols aS []))


      let (change_Write: writing -> writing) = fun writing ->
      match writing with
      | No_Write     -> No_Write
      | Write symbol -> Write (change_Symbol symbol)
(**
      let (synchronize: Action.t list -> Instruction.t) = fun actionS ->
  	  let rec (rec_synchronize: ('r list * 'w list * 'm list) -> Action.t list -> ('r list * 'w list * 'm list)) = fun (reads,writes,moves) actions ->
  		match actions with
  		| [] -> (List.rev reads, List.rev writes, List.rev moves)
  		| action::actions ->
  			(match action with
  			| Nop        -> rec_synchronize ( Nop::reads , Nop::writes , Nop::moves) actions
  			| RWM(r,w,m) -> rec_synchronize ( (change_Read r)::reads , (change_Write w)::writes , m::moves) actions
  			| Simultaneous _ -> failwith "Emulator.Split.synchronize: nested Simultaneous"
  			)
  	  in
  	    let (reads,writes,moves) = rec_synchronize ([],[],[]) actionS
  	    in
  	      Seq[ Action(Simultaneous(reads)) ; Action(Simultaneous(writes)) ; Action(Simultaneous(moves)) ]
**)
      let rec (transitions_emulating: State.t * Action.t * State.t -> Transition.t list) = fun (source,action,target) ->
  	    (match action with
  	    | Nop -> [ (source, Action(Nop), target) ]

  	    | RWM(r,w,m) -> [ (source, Action(RWM((change_Read r), (change_Write w), m)), target) ]

  	    | Simultaneous actions -> [ (source, Action(Nop), target) ]
  	    )

      and (emulate_action: emulator) = fun (source,action,target) ->
  	  let (source,target) =
  	    if source <> target   (* /!\ loop in the emulated TM if source-target *)
  	    then (source,target)
  	    else (State.initial, State.accept)
  	  in
  	    let transitions =  transitions_emulating (source,action,target) in
  	      { Turing_Machine.nop with
  		name = String.concat "" [ "MiseAuPoint" ; Pretty.parentheses (Transition.to_ascii (source,Action action, target)) ] ;
  		initial = source ;
  		accept  = target ;
  		transitions = transitions
  	      }

      (* THE SIMULATOR *)

      let (* USER *) (simulator: simulator) = { name = "MiseAuPoint" ; encoder = encode ;  decoder = decode ; emulator = emulate_action }

    end)




module Binary =
  struct

    (* TRANSLATION OF BANDS *)
    (* The modules Bit and Bits are defined in Alphabet.ml *)

    type encoding = (Symbol.t * Bits.t) list

    let rec foldi i f acc =
        if i <= 0 then acc else foldi (pred i) f (f acc)
    let get_Bits_From_Symbol encoding symbol =
        (fun (a,b) -> b) (List.find (fun (s, _) -> s = symbol) encoding)
    let get_Symbol_From_Bits encoding bits =
        (fun (a,b) -> a) (List.find (fun (_, b) -> b = bits) encoding)

    let build_encoding : Alphabet.t -> encoding = fun alphabet ->
        let (d2b_helper : int -> Symbol.t list) = fun x ->
          match x with
          | 0 -> [Bit.zero]
          | 1 -> [Bit.unit] in
        let rec d2b x y tab =
          match x with
          | 0 -> if (List.length tab = y) then tab else (d2b 0 y (tab@[Bit.zero]))
          | _ -> d2b (x/2) y (tab@(d2b_helper (x mod 2))) in
        List.mapi (fun index symbol -> (symbol, d2b index alphabet.symbol_size_in_bits [])) alphabet.symbols

    let (encode_on_one_band: encoding -> Band.t -> Band.t) = fun encoding band ->

      let rec write_Encoded_Symbol_List band lst =
          match lst with
          | [] -> band
          | h :: t -> write_Encoded_Symbol_List (Band.move_head_right (Band.write h band)) t in
      let rec write_Non_Encoded_Symbol_List encoding band lst =
          match lst with
          | [] -> band
          | head :: tail -> write_Non_Encoded_Symbol_List encoding (write_Encoded_Symbol_List band (get_Bits_From_Symbol encoding head)) tail in

      let alphabet = Alphabet.binary in
      let bandBinary = Band.make alphabet [] in
      let bandBinary = write_Encoded_Symbol_List bandBinary (get_Bits_From_Symbol encoding band.head) in
      let bandBinary = write_Non_Encoded_Symbol_List encoding bandBinary band.right in
      let bandBinary = foldi ((((List.length band.right + List.length band.left) + 1) * band.alphabet.symbol_size_in_bits)) Band.move_head_left bandBinary in
      let bandBinary = write_Non_Encoded_Symbol_List encoding bandBinary (List.rev band.left) in

      bandBinary

    let encode_with : encoding -> Band.t list -> Band.t list = fun encoding bands ->
        List.map(fun band -> encode_on_one_band encoding band) bands

    (* REVERSE TRANSLATION *)

    let (decode_on_one_band: encoding -> Band.t -> Band.t) = fun encoding bandBinary ->

        let rec get_List_First_Element_Tuple_List lst newList =
            match lst with
            | [] -> newList
            | h :: t -> get_List_First_Element_Tuple_List t (((fun (a,b) -> a) h)::newList) in
        let alphabet = Alphabet.make (get_List_First_Element_Tuple_List encoding []) in
        let bandDecode = Band.make alphabet [] in
        let get_Next_Symbol band encoding =
            let rec get_Bits band i size tab =
                if (i = size) then tab else get_Bits (Band.move_head_right band) (i+1) size (tab@[band.head]) in
            let bits = get_Bits band 0 alphabet.symbol_size_in_bits [] in
                get_Symbol_From_Bits encoding bits
        in

        let rec move_Beginning band =
            match band.left with
            | [] -> band
            | _ -> move_Beginning (Band.move_head_left band) in
        let rec write bandBin bandAlpha encoding =
            match bandBin.right with
            | [] -> bandAlpha
            | _ -> write (foldi bandAlpha.alphabet.symbol_size_in_bits Band.move_head_right bandBin) (Band.move_head_right (Band.write (get_Next_Symbol bandBin encoding) bandAlpha)) encoding in

        let decalage = (List.length(bandBinary.right)+1) / alphabet.symbol_size_in_bits in
        let bandBinary = move_Beginning(bandBinary) in
        let bandDecode = write bandBinary bandDecode encoding in
        let bandDecode = foldi decalage Band.move_head_left bandDecode in
            {
                empty with
                left = Band.remove_right_blanks (List.rev bandDecode.left);
                head = bandDecode.head;
                right = Band.remove_right_blanks bandDecode.right;
                alphabet = bandDecode.alphabet
            }

    let decode_with : encoding -> Band.t list -> Band.t list = fun encoding bands ->
        List.map(fun band -> decode_on_one_band encoding band) bands


    (* EMULATION OF TRANSITIONS *)

    let (just_move: encoding -> moving -> Instruction.t list) = fun encoding moving ->
        let instruction = [] in
            List.map(fun null -> Action( RWM (Match(ANY), No_Write, moving))) ((fun (a,b) -> b) (List.hd encoding))

    let (just_read_symbol : encoding -> State.t -> State.t -> Symbol.t -> (Transition.t list * State.t * State.t)) = fun encoding state_Start state_End symbol ->
        let bits = get_Bits_From_Symbol encoding symbol in

        let rec read_Bits bits_To_Read stateOK stateKO =
            match bits_To_Read with
            | [] -> ([],stateOK,stateKO)
            | h::t ->
                let nextstateKO = State.next_from stateOK in
                let nextstateOK = State.next_from nextstateKO in
                let newTransitions =
                    [(stateOK,  Action( RWM(Match(VAL h), No_Write, Right)), nextstateOK);
                    (stateOK,  Action( RWM(Match(BUT h), No_Write, Right)), nextstateKO);
                    (nextstateKO,  Action( RWM(Match(ANY), No_Write, Left)), stateKO)]
                in
                let next_rec = read_Bits t nextstateOK nextstateKO in
                (newTransitions@((fun (a,b,c) -> a) next_rec),((fun (a,b,c) -> b) next_rec),((fun (a,b,c) -> c) next_rec))

        in
        read_Bits bits state_Start state_End

    let (just_write_symbol : encoding -> Symbol.t -> Instruction.t list) = fun encoding symbol ->
        let bits = get_Bits_From_Symbol encoding symbol in
        let rec write_Bits bits_To_Write =
            match bits_To_Write with
            | [] -> []
            | h::t -> Action( RWM(Match(ANY), Write h, Right))::(write_Bits t)
        in
        (just_move encoding Left)@(write_Bits bits)

    let (simple_action : encoding -> State.t -> reading -> writing -> moving -> Transition.t list) = fun encoding state_Start reading writing moving ->
        let symbols_Reading =
            match reading with
            | Match pattern -> Pattern.symbols_of pattern
        in
        let get_Instructions_Writing encoding writing =
            match writing with
            | No_Write     -> [Action(Nop)]
            | Write symbol -> just_write_symbol encoding symbol
        in
        let get_Instructions_Moving encoding moving =
            match moving with
            | Left -> (just_move encoding Left)@(just_move encoding Left)
            | Here -> (just_move encoding Left)
            | Right -> []
        in
        let rec read symbols encoding state_Start state_End =
            match symbols with
            | [] -> ([],state_Start,state_End)
            | h::t ->
                let readed = just_read_symbol encoding state_Start state_End h in
                let next_rec = read t encoding ((fun (a,b,c) -> b) readed) ((fun (a,b,c) -> c) readed) in
                (((fun (a,b,c) -> a) readed)@((fun (a,b,c) -> a) next_rec),((fun (a,b,c) -> b) next_rec),((fun (a,b,c) -> c) next_rec))
        in
        let read_Transitions = read symbols_Reading encoding state_Start State.reject in
        let write_Instructions = get_Instructions_Writing encoding writing in
        let move_Instructions = get_Instructions_Moving encoding moving in
        ((fun (a,b,c) -> a) read_Transitions)@[(((fun (a,b,c) -> b) read_Transitions), Seq(write_Instructions@move_Instructions), State.accept)]
(**
    let (just_read: encoding -> State.t -> reading -> Instruction.t list) = fun encoding state_Start reading ->
        let symbols_Reading =
            match reading with
            | Match pattern -> Pattern.symbols_of pattern
            | _ -> []
        in
        let rec read symbols encoding state_Start state_End =
            match symbols with
            | [] -> ([],state_Start,state_End)
            | h::t ->
                let readed = just_read_symbol encoding state_Start state_End h in
                let next_rec = read t encoding ((fun (a,b,c) -> b) readed) ((fun (a,b,c) -> c) readed) in
                (((fun (a,b,c) -> a) readed)@((fun (a,b,c) -> a) next_rec),((fun (a,b,c) -> b) next_rec),((fun (a,b,c) -> c) next_rec))
        in
        ((fun (a,b,c) -> a) (read symbols_Reading encoding state_Start State.reject))


    let (just_write: encoding -> State.t -> writing -> Instruction.t list) = fun encoding state_Start writing ->
        let get_Instructions_Writing encoding writing =
            match writing with
            | No_Write     -> [Action(Nop)]
            | Write symbol -> just_write_symbol encoding symbol
        in
        (get_Instructions_Writing encoding writing)

    let (just_move:encoding -> State.t -> moving -> Instruction.t list) = fun encoding state_Start moving ->
        let get_Instructions_Moving encoding moving =
            match moving with
            | Left -> (just_move encoding Left)@(just_move encoding Left)
            | Here -> (just_move encoding Left)
            | Right -> []
        in
        (get_Instructions_Moving encoding moving)

    let (synchronize: encoding -> State.t -> Action.t list -> Instruction.t) = fun encoding state_Start actionS ->
	  let rec (rec_synchronize: encoding -> State.t -> ('r list * 'w list * 'm list) -> Action.t list -> ('r list * 'w list * 'm list)) = fun encoding state_Start (reads,writes,moves) actions ->
		match actions with
		| [] -> (List.rev reads, List.rev writes, List.rev moves)
		| action::actions ->
			(match action with
			| Nop        -> rec_synchronize encoding state_Start ( Nop::reads , Nop::writes , Nop::moves) actions
			| RWM(r,w,m) -> rec_synchronize encoding state_Start ( Seq[(just_read encoding source r)]::reads , Seq[(just_write encoding source w)]::writes , Seq[(just_move encoding source m)]::moves) actions
			| Simultaneous _ -> failwith "Emulator.Split.synchronize: nested Simultaneous"
			)
	  in
	    let (reads,writes,moves) = rec_synchronize encoding state_Start ([],[],[]) actionS
	    in
    	      Seq[ Action(Simultaneous(reads)) ; Action(Simultaneous(writes)) ; Action(Simultaneous(moves)) ]
**)
    let rec (emulate_action: encoding -> State.t * Action.t * State.t -> Turing_Machine.t) = fun encoding (source,action,target) ->

        let rec (simultaneous_Actions: encoding -> State.t -> Action.t list -> State.t -> Instruction.t list) = fun encoding source actions target ->
            match actions with
            | [] -> []
            | h::t -> (Run (emulate_action encoding (source, h, target)))::(simultaneous_Actions encoding source t target)
        in

        let (transitions_emulating: encoding -> State.t * Action.t * State.t -> Transition.t list) = fun encoding (source,action,target) ->
    	    (match action with
    	    | Nop -> [ (source, Action(Nop), target) ]

    	    | RWM(r,w,m) -> simple_action encoding source r w m

    	    | Simultaneous actions -> [ (source, Action(Nop), target) ]
    	    )
        in

      let (source,target) =
        if source <> target   (* /!\ loop in the emulated TM if source-target *)
        then (source,target)
        else (State.initial, State.accept)
      in
      let transitions =  transitions_emulating encoding (source,action,target) in
      let () = Printf.printf "\nPRINT TRANSITIONS : :\n" in
      let () = List.iter(fun transition -> Printf.printf "\n%s\n" (Transition.to_ascii transition)) transitions in

    	  { Turing_Machine.nop with
    	    name = String.concat "" [ "Binary" ; Pretty.parentheses (Action.to_ascii action) ] ;
    	    initial = source ;
    	    accept  = target ;
    	    transitions = transitions
    	  }


    (* THE SIMULATOR *)
    let make_simulator : Alphabet.t -> simulator
      = fun alphabet ->
        let encoding = build_encoding alphabet in
        { name = "Binary" ;
          encoder = encode_with encoding ;
          decoder = decode_with encoding ;
          emulator = emulate_action encoding;
        }
  end


(* DEMO *)

open Alphabet

let (demo: unit -> unit) = fun () ->
      print_string "\n\n* DEMO * Emulator.ml:\n" ;
      let alphabet = Alphabet.make [B;Z;U] in
	  let band = Band.make alphabet [U;U;Z;U] in
	  let tm = Turing_Machine.incr in
	    let cfg = Configuration.make tm [ band ] in
	      let _final_cfg = Simulator.log_run_using ([ (* Split.simulator ; *) MiseAuPoint.simulator],[]) cfg
		  in ()

open Printf
open List

type edge = (int*int)
type edge_list = edge array
type state = (int*edge_list)
type state_list = state array
type internals = {mutable name : string ; mutable contents : state_list}


let debug_out = ref stdout
let do_debug = ref false
let debug fmt =
  	let k result = if !do_debug then begin
				output_string !debug_out result ;
    	flush stdout ;
  	end in
  	Printf.kprintf k fmt

let (--) i j =
	let rec aux n acc =
		if n < i then acc else aux (n-1) (n :: acc)
	in aux j []

let sum lst = fold_right (+) lst 0 

let choose_random lst = 
	let size = length lst in
	let choice = Random.int size in
	nth lst choice

class type finite_automata = object
		(* get the automata's name *)
		method get_name : string
		(* Retrieve a state *)
		method get_state : int -> state
		(* Get value for a given state *)
		method get_value : int -> int
		(* Get edges for a given state *)
		method get_edges : int -> edge_list
		(* Get an edge given its number within a state*)
		method get_edge : int -> int -> edge
		(* Get the index of an edge *)
		method get_transition_index : int -> int -> int
		(* Get the destination state of an edge *)
		method get_transition_destination : int -> int -> int
		(* Return all states *)
		method show : state_list
		(* Run automata on input *)
		method run : int list -> int
		(* How many states are there? *)
		method num_states : int
		(* Huw many edges for a given state *)
		method num_edges : int -> int
		(* set the automata's name *)
		method set_name : string -> unit
		(* Set all states at once *)
		method set_states : state_list -> unit
		(* Set the value for a state *)
		method set_value : int -> int -> unit
		(* Set a given edge for a given state *)
		method set_state_edge : int -> int -> edge -> unit 
		(* Set the transition for an edge *)
		method set_edge_transition : int -> int -> int -> unit
		(* set the destination value for an edges *)
		method set_edge_destination : int -> int -> int -> unit
		(* Mutate seld *)
		method mutate : int list -> int list -> unit
		(* Build random fa *)
		method random_build : int -> int list -> int list -> unit
end

class amata : finite_automata = 

	(* Helper methods for random constructing states *)
	let random_edge_list pos_edges pos_states : edge_list  =
		let tmp_list = ref [] in
		iter (fun i -> if (Random.int 2) = 1 
						then tmp_list := i :: !tmp_list ) pos_edges ;
		if !tmp_list = [] then tmp_list := [choose_random pos_edges] ;
		Array.map (fun el -> (el, (choose_random pos_states))) (Array.of_list !tmp_list) in 
	let random_state pos_vals pos_edges pos_states : state = 
		let choice = choose_random pos_vals in
		(choice,(random_edge_list pos_edges pos_states)) in
	let random_state_list len pos_vals pos_edges pos_states : state_list =
		let lst = 0--len in
		Array.map (fun _ -> (random_state pos_vals pos_edges pos_states)) (Array.of_list lst) in

	let states = { name = "default"; contents = [|(0,[|(0,0)|])|] } in

	object(self)
		method get_name =
			states.name
		method get_value num =
			let (v,edges) = self#get_state num in
			v
		method set_name str = 
			states.name <- str 
		method set_states lst =
			states.contents <- lst 
		method get_edges state =
			let (s,es) = (self#get_state state) in es
		method get_edge state edge =
			let edges = self#get_edges state in
			edges.(edge)
		method num_states =
			Array.length states.contents
		method num_edges snum =
			let (v,edges) = (self#get_state snum) in
			Array.length edges
		method set_value snum va =
			let (o_va,o_el) = states.contents.(snum) in
			(states.contents).(snum) <- (va,o_el) ;
			()
		method set_state_edge state enum new_e =
			let (_,old_edges) = self#get_state state in
			try
				old_edges.(enum) <- new_e ;
			with
				| Invalid_argument x -> 
					printf "Attempting to change an edge out of bounds.\n" ;
		method set_edge_transition state edge value =
			let old_edges = self#get_edges state in
			let (t,d) = old_edges.(edge) in
			old_edges.(edge) <- (value,d) ;
		method set_edge_destination state edge value =
			let old_edges = self#get_edges state in
			let (t,d) = old_edges.(edge) in
			old_edges.(edge) <- (t,value) ;
		method get_state num =
			(states.contents).(num)
		method show =
			states.contents
		method get_transition_index state transition =
			try
				let elist = self#get_edges state in
				let (place,(e,d)) = find (fun p -> let (id,(e,d)) = p in transition = e) 
					(map2 (fun x id -> (id,x)) (Array.to_list elist) (0--((Array.length elist)-1))) in
				place
			with
				| Not_found -> -1
		method get_transition_destination state transition =
			try
				let elist = self#get_edges state in
				let (place,(e,d)) = find (fun p -> let (id,(e,d)) = p in transition = e) 
					(map2 (fun x id -> (id,x)) (Array.to_list elist) (0--((Array.length elist)-1))) in
				d
			with 
				| Not_found -> state
		method random_build mx_st o_l o_v =
			let total_states = Random.int mx_st in
			let pos_states = 0 -- total_states in
			states.contents <- (random_state_list total_states o_v o_l pos_states) ; 
		method mutate o_l o_v =
			let choice = Random.int 3 in
			match choice with
			| 0 -> 
				debug "Deleting state\n" ;
				(* Delete state *)
				let len = self#num_states in
				if not (len <= 1) then
					let to_del_num = Random.int len in
					let new_arr = Array.make (len-1) (0,[|(0,0)|]) in
					let correc = ref 0 in
					for i = 0 to (len-2) do (* Len-1 is last in old, so one less than that *)
						if i = to_del_num then correc := 1 ;
						new_arr.(i) <- self#get_state (i + !correc) ;
					done ;
					let final_arr = Array.map
						(fun el ->
							let (v,edges) = el in
							let elist = Array.to_list edges in
							let newl = filter (fun x -> let (t,d) = x in not (d = len-1)) 
								elist in
							(v,(Array.of_list newl))) new_arr in 
					states.contents <- final_arr
				else
					self#mutate o_l o_v  
			| 1 -> 
					debug "Inserting state\n" ;
					(* insert state *)
					let len = self#num_states in
					let new_s = random_state o_l o_v (0--(len+1)) in
					let cpy = states.contents in
					Array.iteri
						(fun i el ->
							let (v,edges) = el in
							let add_transition = Random.int 2 in
							match add_transition with
							| 0 -> ()
							| 1 -> 
								let new_l = choose_random o_l in
								let next_e = [|(new_l,len+1)|] in
								let new_edge_list = Array.append edges next_e in
								states.contents.(i) <- (v,new_edge_list) ;
							| _ -> ()
							) states.contents ;
						states.contents <- Array.append cpy [|new_s|] ;
			| 2 ->
					(* change existing state *)
					let len = self#num_states in
					let to_change = Random.int len in
					let what_doing = Random.int 5 in
					debug  "Changing existing state(%d)\n" to_change ;
					match what_doing with
					| 0 -> 
							(* Change a value *)
							debug "Changing a value\n" ;
							let new_v = choose_random o_v in
							self#set_value to_change new_v 
					| 1 -> 
							(* Change a transition *)
							debug "Changing a transition\n" ;
							let new_t = choose_random o_l in
							let edge_pos = self#num_edges to_change in
							if edge_pos > 0 then
								let what_edge = Random.int edge_pos in
									debug "edge:%d,new:%d\n" what_edge new_t ;
									self#set_edge_transition to_change what_edge new_t
								else
									self#mutate o_l o_v 
					| 2 -> 
							(* Change a destination *)
							debug "Changing a destination:\n" ;
							let new_d = Random.int len in
							let edge_pos = self#num_edges to_change in
							if edge_pos > 0 then
								let what_edge = Random.int edge_pos in
									debug  "edge:%d,destination:%d\n" what_edge new_d;
									self#set_edge_destination to_change what_edge new_d
								else self#mutate o_l o_v  
					| 3 ->
							(* Add an edge *)
							debug "Adding an edge\n" ; 
							let (v,edges) = self#get_state to_change in
							let new_t = choose_random o_l in
							let new_d = Random.int len in
							let new_edges = Array.append edges [|(new_t,new_d)|] in
							states.contents.(to_change) <- (v,new_edges)
					| 4 ->
							(* Delete an edge *)
							debug "Deleting an edge\n" ;
							let (v,edges) = self#get_state to_change in
							let edge_pos = self#num_edges to_change in
							if edge_pos > 0 then
								let what_edge = (self#get_edge to_change (Random.int edge_pos)) in
								let edge_list = Array.to_list edges in
								let new_edges = Array.of_list (filter (fun x -> not (x = what_edge)) edge_list) in
									states.contents.(to_change) <- (v,new_edges)
								else
									self#mutate o_l o_v
					| _ -> ()
		method run (input_lst : int list) =
			let (ival,_) = self#get_state 0 in
			let value = ref ival in
			let state = ref 0 in
			let rec parse_input i =
				(match (self#get_state !state) with
				| (o_val, _) ->
						(*value := o_val ;*) 
						let newstate = self#get_transition_destination !state i in
						try 
								let (v,_) = self#get_state newstate in 
								state := newstate ; 
								value := v ;
								()
						with (* change destination if it doesn't exist *)
							| Invalid_argument x -> 
								let place = self#get_transition_index !state i in
								(self#set_edge_destination !state place (Random.int (self#num_states))) ; 
								parse_input i ; ) in
			iter parse_input input_lst ;
			!value
end

let pop = ref []
let state_size = ref 10
let o_l = ref [0;1]
let o_v = ref [0;1]
let popsize = ref 50
let max_fit = ref 4
let num_gens = ref 10000

type population = finite_automata list
type evaluated_pop = (finite_automata*int) list

let new_pop size state_size o_l o_v : population =
	let pop = map (fun i -> new amata) (0--(size-1)) in
	let init = map (fun i -> (i#random_build state_size o_l o_v) ; i) pop in
	init

let mutate_pop (pop : population) o_l o_v : population =
	iter (fun i -> i#mutate o_l o_v) pop ;
	pop

let eval_pop func pop : evaluated_pop =
	let eval = map (fun p -> (p,(func p))) pop in
	printf "Generation fitness:\n" ;
	iter (fun (v,f) -> printf "%d," f) eval ;
	let avg = ((fold_right (+.) (map (fun (x,y) -> (float_of_int y)) eval) 0.0) /. (float_of_int (length eval))) in
	printf "\nAverage:%g\n" avg ; 
	eval

let tour_select (e_pop : population) func num : population =
	let lineup1 = map (fun x -> choose_random e_pop) (0--(num-1)) in
	let lineup2 = map (fun x -> choose_random e_pop) (0--(num-1)) in
	let lineup3 = map (fun x -> choose_random e_pop) (0--(num-1)) in
	let winners l1 l2 = map2 
		(fun x y ->
			(func x y)) l1 l2 in
	let w1 = winners lineup1 lineup2 in
	let wf = winners lineup3 w1 in
	wf

let test_eval inputs outputs indiv1 indiv2 =
	let test i = map (fun x -> i#run x) inputs in
	let right res = map2 (fun x y -> if x = y then 1 else 0) res outputs in
	let res1 = test indiv1 in
	let res2 = test indiv2 in
	let f1 = sum (right res1) in
	let f2 = sum (right res2) in
	if f1 > f2 then indiv1 else indiv2

let play_game games indiv1 indiv2 =
	let p1score = ref 0 in
	let p2score = ref 0 in
	let turn = ref 0 in
	let getscore pair = match pair with
		| (0,0) -> (10,10)
		| (0,1) -> (0,5)
		| (1,0) -> (5,0)
		| (1,1) -> (1,1)
		| _ -> printf "What?\n" ; (0,0) in
	let (playfirst,playsecond) = 
		if (Random.int 2) = 0 then (indiv1,indiv2) else (indiv2,indiv1) in
	turn  := playfirst#get_value 0 ;
	for i = 1 to games do
		let next = playsecond#run [!turn] in
		let (p1s,p2s) = getscore (!turn,next) in
		p1score := !p1score + p1s ;
		p2score := !p2score + p2s ;
		turn := playfirst#run [next] ;
	done ;
	printf "%d,%d\n" !p1score !p2score ;
	if !p1score > !p2score then playfirst else playsecond

let statistics (pop : population) func =
	let eval_pop = map (fun p -> (p,(func p))) pop in
	let avg = ((fold_right (+.) (map (fun (x,y) -> (float_of_int y)) eval_pop) 0.0) /. (float_of_int (length eval_pop))) in
	printf "Average:%g\n" avg ; 
	let bstlst = sort (fun (x,fx) (y,fy) -> fy - fx) eval_pop in
	let (bst,fbst) = nth bstlst 0 in
	printf "Best:%d\n" fbst ;
	(bst,fbst) 
	

let rec evolve_cycle gen func pop  =
	printf "Generation %d\n" gen ;
	let select = tour_select pop func (!popsize / 2) in
	let newp = new_pop (!popsize / 2) !state_size !o_l !o_v in
	let next = select @ newp in
	let mutate = map 
		(fun x -> 
			let rand = Random.int 3 in 
			if rand = 0 then 
			begin 
				x#mutate !o_l !o_v; 
				x 
			end 
			else x) next in
		if !num_gens = gen then 
			pop
		else	
			evolve_cycle (gen+1) func mutate  

let my = new amata 
let pop = new_pop !popsize !state_size !o_l !o_v
let xor = test_eval [[0;0];[0;1];[1;0];[1;1]] [0;1;1;0] 
let even_or_odd_zeros = test_eval [[0;1];[0;1;0];[1;1;0];[0;0;0;1];[0;1;0;1];[0;0;1;1;]] [0;1;0;0;1;1]

let main =
	my#random_build 4 [0;1] [0;1] ;
	max_fit := 6 ;
	evolve_cycle 0 (play_game 10) pop ;

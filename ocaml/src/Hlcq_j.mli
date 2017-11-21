(* Auto-generated from "Hlcq.atd" *)


type loc = Hlcq_t.loc = {
  hlcq_offset (*atd offset *): int;
  hlcq_line (*atd line *): int;
  hlcq_column (*atd column *): int
}

type location = Hlcq_t.location = {
  hlcq_start (*atd start *): loc;
  hlcq_end (*atd end *): loc
}

type json = Yojson.Basic.json

type select = Hlcq_t.select = {
  hlcq_s_kind (*atd kind *): string;
  hlcq_s_resource (*atd resource *): string;
  hlcq_s_where (*atd where *): json option;
  hlcq_s_limit (*atd limit *): json option;
  hlcq_s_skip (*atd skip *): json option;
  hlcq_s_orderBy (*atd orderBy *): json option;
  hlcq_s_location (*atd location *): location
}

type ident = Hlcq_t.ident = {
  hlcq_i_kind (*atd kind *): string;
  hlcq_i_name (*atd name *): string
}

type query = Hlcq_t.query = {
  hlcq_q_kind (*atd kind *): string;
  hlcq_q_identifier (*atd identifier *): ident;
  hlcq_q_description (*atd description *): string;
  hlcq_q_select (*atd select *): select;
  hlcq_q_location (*atd location *): location
}

val write_loc :
  Bi_outbuf.t -> loc -> unit
  (** Output a JSON value of type {!loc}. *)

val string_of_loc :
  ?len:int -> loc -> string
  (** Serialize a value of type {!loc}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_loc :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> loc
  (** Input JSON data of type {!loc}. *)

val loc_of_string :
  string -> loc
  (** Deserialize JSON data of type {!loc}. *)

val write_location :
  Bi_outbuf.t -> location -> unit
  (** Output a JSON value of type {!location}. *)

val string_of_location :
  ?len:int -> location -> string
  (** Serialize a value of type {!location}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_location :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> location
  (** Input JSON data of type {!location}. *)

val location_of_string :
  string -> location
  (** Deserialize JSON data of type {!location}. *)

val write_json :
  Bi_outbuf.t -> json -> unit
  (** Output a JSON value of type {!json}. *)

val string_of_json :
  ?len:int -> json -> string
  (** Serialize a value of type {!json}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_json :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> json
  (** Input JSON data of type {!json}. *)

val json_of_string :
  string -> json
  (** Deserialize JSON data of type {!json}. *)

val write_select :
  Bi_outbuf.t -> select -> unit
  (** Output a JSON value of type {!select}. *)

val string_of_select :
  ?len:int -> select -> string
  (** Serialize a value of type {!select}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_select :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> select
  (** Input JSON data of type {!select}. *)

val select_of_string :
  string -> select
  (** Deserialize JSON data of type {!select}. *)

val write_ident :
  Bi_outbuf.t -> ident -> unit
  (** Output a JSON value of type {!ident}. *)

val string_of_ident :
  ?len:int -> ident -> string
  (** Serialize a value of type {!ident}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_ident :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> ident
  (** Input JSON data of type {!ident}. *)

val ident_of_string :
  string -> ident
  (** Deserialize JSON data of type {!ident}. *)

val write_query :
  Bi_outbuf.t -> query -> unit
  (** Output a JSON value of type {!query}. *)

val string_of_query :
  ?len:int -> query -> string
  (** Serialize a value of type {!query}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_query :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> query
  (** Input JSON data of type {!query}. *)

val query_of_string :
  string -> query
  (** Deserialize JSON data of type {!query}. *)


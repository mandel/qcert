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

let write_loc : _ -> loc -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"offset\":";
    (
      Yojson.Safe.write_int
    )
      ob x.hlcq_offset;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"line\":";
    (
      Yojson.Safe.write_int
    )
      ob x.hlcq_line;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"column\":";
    (
      Yojson.Safe.write_int
    )
      ob x.hlcq_column;
    Bi_outbuf.add_char ob '}';
)
let string_of_loc ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_loc ob x;
  Bi_outbuf.contents ob
let read_loc = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_hlcq_offset = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_line = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_column = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 4 -> (
                if String.unsafe_get s pos = 'l' && String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'e' then (
                  1
                )
                else (
                  -1
                )
              )
            | 6 -> (
                match String.unsafe_get s pos with
                  | 'c' -> (
                      if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'l' && String.unsafe_get s (pos+3) = 'u' && String.unsafe_get s (pos+4) = 'm' && String.unsafe_get s (pos+5) = 'n' then (
                        2
                      )
                      else (
                        -1
                      )
                    )
                  | 'o' -> (
                      if String.unsafe_get s (pos+1) = 'f' && String.unsafe_get s (pos+2) = 'f' && String.unsafe_get s (pos+3) = 's' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 't' then (
                        0
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_hlcq_offset := (
              (
                Ag_oj_run.read_int
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_hlcq_line := (
              (
                Ag_oj_run.read_int
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | 2 ->
            field_hlcq_column := (
              (
                Ag_oj_run.read_int
              ) p lb
            );
            bits0 := !bits0 lor 0x4;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 4 -> (
                  if String.unsafe_get s pos = 'l' && String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'e' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 6 -> (
                  match String.unsafe_get s pos with
                    | 'c' -> (
                        if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'l' && String.unsafe_get s (pos+3) = 'u' && String.unsafe_get s (pos+4) = 'm' && String.unsafe_get s (pos+5) = 'n' then (
                          2
                        )
                        else (
                          -1
                        )
                      )
                    | 'o' -> (
                        if String.unsafe_get s (pos+1) = 'f' && String.unsafe_get s (pos+2) = 'f' && String.unsafe_get s (pos+3) = 's' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 't' then (
                          0
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_hlcq_offset := (
                (
                  Ag_oj_run.read_int
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_hlcq_line := (
                (
                  Ag_oj_run.read_int
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | 2 ->
              field_hlcq_column := (
                (
                  Ag_oj_run.read_int
                ) p lb
              );
              bits0 := !bits0 lor 0x4;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x7 then Ag_oj_run.missing_fields p [| !bits0 |] [| "offset"; "line"; "column" |];
        (
          {
            hlcq_offset = !field_hlcq_offset;
            hlcq_line = !field_hlcq_line;
            hlcq_column = !field_hlcq_column;
          }
         : loc)
      )
)
let loc_of_string s =
  read_loc (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_location : _ -> location -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"start\":";
    (
      write_loc
    )
      ob x.hlcq_start;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"end\":";
    (
      write_loc
    )
      ob x.hlcq_end;
    Bi_outbuf.add_char ob '}';
)
let string_of_location ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_location ob x;
  Bi_outbuf.contents ob
let read_location = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_hlcq_start = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_end = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 3 -> (
                if String.unsafe_get s pos = 'e' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 'd' then (
                  1
                )
                else (
                  -1
                )
              )
            | 5 -> (
                if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 't' && String.unsafe_get s (pos+2) = 'a' && String.unsafe_get s (pos+3) = 'r' && String.unsafe_get s (pos+4) = 't' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_hlcq_start := (
              (
                read_loc
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_hlcq_end := (
              (
                read_loc
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 3 -> (
                  if String.unsafe_get s pos = 'e' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 'd' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 5 -> (
                  if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 't' && String.unsafe_get s (pos+2) = 'a' && String.unsafe_get s (pos+3) = 'r' && String.unsafe_get s (pos+4) = 't' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_hlcq_start := (
                (
                  read_loc
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_hlcq_end := (
                (
                  read_loc
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "start"; "end" |];
        (
          {
            hlcq_start = !field_hlcq_start;
            hlcq_end = !field_hlcq_end;
          }
         : location)
      )
)
let location_of_string s =
  read_location (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_json = (
  Yojson.Basic.write_json
)
let string_of_json ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_json ob x;
  Bi_outbuf.contents ob
let read_json = (
  Yojson.Basic.read_json
)
let json_of_string s =
  read_json (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write__1 = (
  Ag_oj_run.write_nullable (
    write_json
  )
)
let string_of__1 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__1 ob x;
  Bi_outbuf.contents ob
let read__1 = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    (if Yojson.Safe.read_null_if_possible p lb then None
    else Some ((
      read_json
    ) p lb) : _ option)
)
let _1_of_string s =
  read__1 (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_select : _ -> select -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"kind\":";
    (
      Yojson.Safe.write_string
    )
      ob x.hlcq_s_kind;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"resource\":";
    (
      Yojson.Safe.write_string
    )
      ob x.hlcq_s_resource;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"where\":";
    (
      write__1
    )
      ob x.hlcq_s_where;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"limit\":";
    (
      write__1
    )
      ob x.hlcq_s_limit;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"skip\":";
    (
      write__1
    )
      ob x.hlcq_s_skip;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"orderBy\":";
    (
      write__1
    )
      ob x.hlcq_s_orderBy;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"location\":";
    (
      write_location
    )
      ob x.hlcq_s_location;
    Bi_outbuf.add_char ob '}';
)
let string_of_select ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_select ob x;
  Bi_outbuf.contents ob
let read_select = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_hlcq_s_kind = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_s_resource = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_s_where = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_s_limit = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_s_skip = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_s_orderBy = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_s_location = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 4 -> (
                match String.unsafe_get s pos with
                  | 'k' -> (
                      if String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'd' then (
                        0
                      )
                      else (
                        -1
                      )
                    )
                  | 's' -> (
                      if String.unsafe_get s (pos+1) = 'k' && String.unsafe_get s (pos+2) = 'i' && String.unsafe_get s (pos+3) = 'p' then (
                        4
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | 5 -> (
                match String.unsafe_get s pos with
                  | 'l' -> (
                      if String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 't' then (
                        3
                      )
                      else (
                        -1
                      )
                    )
                  | 'w' -> (
                      if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 'e' && String.unsafe_get s (pos+3) = 'r' && String.unsafe_get s (pos+4) = 'e' then (
                        2
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | 7 -> (
                if String.unsafe_get s pos = 'o' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'd' && String.unsafe_get s (pos+3) = 'e' && String.unsafe_get s (pos+4) = 'r' && String.unsafe_get s (pos+5) = 'B' && String.unsafe_get s (pos+6) = 'y' then (
                  5
                )
                else (
                  -1
                )
              )
            | 8 -> (
                match String.unsafe_get s pos with
                  | 'l' -> (
                      if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'c' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
                        6
                      )
                      else (
                        -1
                      )
                    )
                  | 'r' -> (
                      if String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'o' && String.unsafe_get s (pos+4) = 'u' && String.unsafe_get s (pos+5) = 'r' && String.unsafe_get s (pos+6) = 'c' && String.unsafe_get s (pos+7) = 'e' then (
                        1
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_hlcq_s_kind := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_hlcq_s_resource := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | 2 ->
            field_hlcq_s_where := (
              (
                read__1
              ) p lb
            );
            bits0 := !bits0 lor 0x4;
          | 3 ->
            field_hlcq_s_limit := (
              (
                read__1
              ) p lb
            );
            bits0 := !bits0 lor 0x8;
          | 4 ->
            field_hlcq_s_skip := (
              (
                read__1
              ) p lb
            );
            bits0 := !bits0 lor 0x10;
          | 5 ->
            field_hlcq_s_orderBy := (
              (
                read__1
              ) p lb
            );
            bits0 := !bits0 lor 0x20;
          | 6 ->
            field_hlcq_s_location := (
              (
                read_location
              ) p lb
            );
            bits0 := !bits0 lor 0x40;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 4 -> (
                  match String.unsafe_get s pos with
                    | 'k' -> (
                        if String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'd' then (
                          0
                        )
                        else (
                          -1
                        )
                      )
                    | 's' -> (
                        if String.unsafe_get s (pos+1) = 'k' && String.unsafe_get s (pos+2) = 'i' && String.unsafe_get s (pos+3) = 'p' then (
                          4
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | 5 -> (
                  match String.unsafe_get s pos with
                    | 'l' -> (
                        if String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 't' then (
                          3
                        )
                        else (
                          -1
                        )
                      )
                    | 'w' -> (
                        if String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 'e' && String.unsafe_get s (pos+3) = 'r' && String.unsafe_get s (pos+4) = 'e' then (
                          2
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | 7 -> (
                  if String.unsafe_get s pos = 'o' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'd' && String.unsafe_get s (pos+3) = 'e' && String.unsafe_get s (pos+4) = 'r' && String.unsafe_get s (pos+5) = 'B' && String.unsafe_get s (pos+6) = 'y' then (
                    5
                  )
                  else (
                    -1
                  )
                )
              | 8 -> (
                  match String.unsafe_get s pos with
                    | 'l' -> (
                        if String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'c' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
                          6
                        )
                        else (
                          -1
                        )
                      )
                    | 'r' -> (
                        if String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'o' && String.unsafe_get s (pos+4) = 'u' && String.unsafe_get s (pos+5) = 'r' && String.unsafe_get s (pos+6) = 'c' && String.unsafe_get s (pos+7) = 'e' then (
                          1
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_hlcq_s_kind := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_hlcq_s_resource := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | 2 ->
              field_hlcq_s_where := (
                (
                  read__1
                ) p lb
              );
              bits0 := !bits0 lor 0x4;
            | 3 ->
              field_hlcq_s_limit := (
                (
                  read__1
                ) p lb
              );
              bits0 := !bits0 lor 0x8;
            | 4 ->
              field_hlcq_s_skip := (
                (
                  read__1
                ) p lb
              );
              bits0 := !bits0 lor 0x10;
            | 5 ->
              field_hlcq_s_orderBy := (
                (
                  read__1
                ) p lb
              );
              bits0 := !bits0 lor 0x20;
            | 6 ->
              field_hlcq_s_location := (
                (
                  read_location
                ) p lb
              );
              bits0 := !bits0 lor 0x40;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x7f then Ag_oj_run.missing_fields p [| !bits0 |] [| "kind"; "resource"; "where"; "limit"; "skip"; "orderBy"; "location" |];
        (
          {
            hlcq_s_kind = !field_hlcq_s_kind;
            hlcq_s_resource = !field_hlcq_s_resource;
            hlcq_s_where = !field_hlcq_s_where;
            hlcq_s_limit = !field_hlcq_s_limit;
            hlcq_s_skip = !field_hlcq_s_skip;
            hlcq_s_orderBy = !field_hlcq_s_orderBy;
            hlcq_s_location = !field_hlcq_s_location;
          }
         : select)
      )
)
let select_of_string s =
  read_select (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_ident : _ -> ident -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"kind\":";
    (
      Yojson.Safe.write_string
    )
      ob x.hlcq_i_kind;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"name\":";
    (
      Yojson.Safe.write_string
    )
      ob x.hlcq_i_name;
    Bi_outbuf.add_char ob '}';
)
let string_of_ident ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_ident ob x;
  Bi_outbuf.contents ob
let read_ident = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_hlcq_i_kind = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_i_name = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          if len = 4 then (
            match String.unsafe_get s pos with
              | 'k' -> (
                  if String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'd' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 'n' -> (
                  if String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'e' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
          )
          else (
            -1
          )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_hlcq_i_kind := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_hlcq_i_name := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            if len = 4 then (
              match String.unsafe_get s pos with
                | 'k' -> (
                    if String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'd' then (
                      0
                    )
                    else (
                      -1
                    )
                  )
                | 'n' -> (
                    if String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'e' then (
                      1
                    )
                    else (
                      -1
                    )
                  )
                | _ -> (
                    -1
                  )
            )
            else (
              -1
            )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_hlcq_i_kind := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_hlcq_i_name := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x3 then Ag_oj_run.missing_fields p [| !bits0 |] [| "kind"; "name" |];
        (
          {
            hlcq_i_kind = !field_hlcq_i_kind;
            hlcq_i_name = !field_hlcq_i_name;
          }
         : ident)
      )
)
let ident_of_string s =
  read_ident (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_query : _ -> query -> _ = (
  fun ob x ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"kind\":";
    (
      Yojson.Safe.write_string
    )
      ob x.hlcq_q_kind;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"identifier\":";
    (
      write_ident
    )
      ob x.hlcq_q_identifier;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"description\":";
    (
      Yojson.Safe.write_string
    )
      ob x.hlcq_q_description;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"select\":";
    (
      write_select
    )
      ob x.hlcq_q_select;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"location\":";
    (
      write_location
    )
      ob x.hlcq_q_location;
    Bi_outbuf.add_char ob '}';
)
let string_of_query ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_query ob x;
  Bi_outbuf.contents ob
let read_query = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_hlcq_q_kind = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_q_identifier = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_q_description = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_q_select = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_hlcq_q_location = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 4 -> (
                if String.unsafe_get s pos = 'k' && String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'd' then (
                  0
                )
                else (
                  -1
                )
              )
            | 6 -> (
                if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'l' && String.unsafe_get s (pos+3) = 'e' && String.unsafe_get s (pos+4) = 'c' && String.unsafe_get s (pos+5) = 't' then (
                  3
                )
                else (
                  -1
                )
              )
            | 8 -> (
                if String.unsafe_get s pos = 'l' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'c' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
                  4
                )
                else (
                  -1
                )
              )
            | 10 -> (
                if String.unsafe_get s pos = 'i' && String.unsafe_get s (pos+1) = 'd' && String.unsafe_get s (pos+2) = 'e' && String.unsafe_get s (pos+3) = 'n' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'f' && String.unsafe_get s (pos+7) = 'i' && String.unsafe_get s (pos+8) = 'e' && String.unsafe_get s (pos+9) = 'r' then (
                  1
                )
                else (
                  -1
                )
              )
            | 11 -> (
                if String.unsafe_get s pos = 'd' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'c' && String.unsafe_get s (pos+4) = 'r' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'p' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'i' && String.unsafe_get s (pos+9) = 'o' && String.unsafe_get s (pos+10) = 'n' then (
                  2
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Ag_oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_hlcq_q_kind := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x1;
          | 1 ->
            field_hlcq_q_identifier := (
              (
                read_ident
              ) p lb
            );
            bits0 := !bits0 lor 0x2;
          | 2 ->
            field_hlcq_q_description := (
              (
                Ag_oj_run.read_string
              ) p lb
            );
            bits0 := !bits0 lor 0x4;
          | 3 ->
            field_hlcq_q_select := (
              (
                read_select
              ) p lb
            );
            bits0 := !bits0 lor 0x8;
          | 4 ->
            field_hlcq_q_location := (
              (
                read_location
              ) p lb
            );
            bits0 := !bits0 lor 0x10;
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 4 -> (
                  if String.unsafe_get s pos = 'k' && String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'd' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 6 -> (
                  if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'l' && String.unsafe_get s (pos+3) = 'e' && String.unsafe_get s (pos+4) = 'c' && String.unsafe_get s (pos+5) = 't' then (
                    3
                  )
                  else (
                    -1
                  )
                )
              | 8 -> (
                  if String.unsafe_get s pos = 'l' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'c' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'o' && String.unsafe_get s (pos+7) = 'n' then (
                    4
                  )
                  else (
                    -1
                  )
                )
              | 10 -> (
                  if String.unsafe_get s pos = 'i' && String.unsafe_get s (pos+1) = 'd' && String.unsafe_get s (pos+2) = 'e' && String.unsafe_get s (pos+3) = 'n' && String.unsafe_get s (pos+4) = 't' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'f' && String.unsafe_get s (pos+7) = 'i' && String.unsafe_get s (pos+8) = 'e' && String.unsafe_get s (pos+9) = 'r' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 11 -> (
                  if String.unsafe_get s pos = 'd' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'c' && String.unsafe_get s (pos+4) = 'r' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'p' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'i' && String.unsafe_get s (pos+9) = 'o' && String.unsafe_get s (pos+10) = 'n' then (
                    2
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Ag_oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_hlcq_q_kind := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x1;
            | 1 ->
              field_hlcq_q_identifier := (
                (
                  read_ident
                ) p lb
              );
              bits0 := !bits0 lor 0x2;
            | 2 ->
              field_hlcq_q_description := (
                (
                  Ag_oj_run.read_string
                ) p lb
              );
              bits0 := !bits0 lor 0x4;
            | 3 ->
              field_hlcq_q_select := (
                (
                  read_select
                ) p lb
              );
              bits0 := !bits0 lor 0x8;
            | 4 ->
              field_hlcq_q_location := (
                (
                  read_location
                ) p lb
              );
              bits0 := !bits0 lor 0x10;
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        if !bits0 <> 0x1f then Ag_oj_run.missing_fields p [| !bits0 |] [| "kind"; "identifier"; "description"; "select"; "location" |];
        (
          {
            hlcq_q_kind = !field_hlcq_q_kind;
            hlcq_q_identifier = !field_hlcq_q_identifier;
            hlcq_q_description = !field_hlcq_q_description;
            hlcq_q_select = !field_hlcq_q_select;
            hlcq_q_location = !field_hlcq_q_location;
          }
         : query)
      )
)
let query_of_string s =
  read_query (Yojson.Safe.init_lexer ()) (Lexing.from_string s)

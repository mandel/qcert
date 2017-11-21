(* Auto-generated from "Hlcq.atd" *)


type loc = {
  hlcq_offset (*atd offset *): int;
  hlcq_line (*atd line *): int;
  hlcq_column (*atd column *): int
}

type location = {
  hlcq_start (*atd start *): loc;
  hlcq_end (*atd end *): loc
}

type json = Yojson.Basic.json

type select = {
  hlcq_s_kind (*atd kind *): string;
  hlcq_s_resource (*atd resource *): string;
  hlcq_s_where (*atd where *): json option;
  hlcq_s_limit (*atd limit *): json option;
  hlcq_s_skip (*atd skip *): json option;
  hlcq_s_orderBy (*atd orderBy *): json option;
  hlcq_s_location (*atd location *): location
}

type ident = {
  hlcq_i_kind (*atd kind *): string;
  hlcq_i_name (*atd name *): string
}

type query = {
  hlcq_q_kind (*atd kind *): string;
  hlcq_q_identifier (*atd identifier *): ident;
  hlcq_q_description (*atd description *): string;
  hlcq_q_select (*atd select *): select;
  hlcq_q_location (*atd location *): location
}

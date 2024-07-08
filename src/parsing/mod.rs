use std::f64;
use peg;

#[derive(Debug, PartialEq)]
pub enum Literal {
    String(String),
    Number(f64),
}

#[derive(Debug, PartialEq)]
pub enum StatementRet {
    VarIdOnly(String),
    VarLiteralAndId((String, Literal)),
    Class(String, Vec<StatementRet>),
}

peg::parser! {
    pub grammar ast_parser() for str {
        rule _ = quiet!{[' ' | '\n' | '\t']*}

        rule identifier() -> String
            = _ s:$((['a'..='z' | 'A'..='Z' | '_'])+) _ {s.to_owned()}

        rule literal_string() -> Literal
            = "\"" s:$(identifier()) "\"" {Literal::String(s.to_owned())}

        rule literal_number() -> Literal // Only scalar type in Lox is f64
            = n:$(['0'..='9']+) {?
                let inner = {n.parse::<f64>().or(Err("f64"))?};
                Ok(Literal::Number(inner))
            }

        pub rule literal() -> Literal
            = literal_number() / literal_string()

        // Statements
        pub rule var_empty() -> String
            = "var" _ s:identifier() _ {s}
        
        pub rule var_init() -> (String, Literal)
            = e:var_empty() _ "=" _ v:literal() _ {(e, v)}

        rule class_statements() -> Vec<StatementRet>
            = s:statement() ** _ {s}

        pub rule class() -> (String, Vec<StatementRet>)
            = "class" _ c:identifier() _ "{" _ stmts:class_statements() _ "}" {(c.to_owned(), stmts)}
        // Core
        pub rule statement() -> StatementRet
            = i:var_init() ";" { StatementRet::VarLiteralAndId(i) }
              / e:var_empty() ";" { StatementRet::VarIdOnly(e) }
              / c:class() {StatementRet::Class(c.0, c.1)}
        //
        
    }
}
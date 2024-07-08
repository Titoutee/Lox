
pub mod parsing;
use parsing::Literal;

pub fn run(src: &str) {
    todo!()
}

#[cfg(test)]
mod tests {
    use crate::{parsing::{ast_parser, StatementRet}, run};
    use super::Literal;
    
    #[test]
    fn var_empty() {
        let var_empty = "var compound;";
        match ast_parser::statement(var_empty).unwrap() {
            StatementRet::VarIdOnly(id) => {
                assert_eq!(id, String::from("compound"));
            }
            _ => panic!("Uninit should not contain a literal!"),
        }
    }

    #[test]
    fn var_empty_ill() {
        let var_empty = "var compound ;";
        match ast_parser::statement(var_empty).unwrap() {
            StatementRet::VarIdOnly(id) => {
                assert_eq!(id, String::from("compound"));
            }
            _ => panic!("Uninit should not contain a literal!"),
        }
    }

    #[test]
    #[should_panic]
    fn var_empty_bad() {
        let var_empty = "va r compou nd;"; // Badly formed
        match ast_parser::statement(var_empty).unwrap() {
            StatementRet::VarIdOnly(id) => {
                assert_eq!(id, String::from("compound"));
            }
            _ => panic!("Uninit should not contain a literal!"),
        }
    }

    #[test]
    fn literal_string() {
        let string = "\"hey\"";
        match ast_parser::literal(string).unwrap() {
            Literal::String(s) => {
                assert_eq!(s, String::from("hey"));
            },
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    fn literal_number() {
        let number = "6543";
        match ast_parser::literal(number).unwrap() {
            Literal::Number(n) => {
                assert_eq!(n, 6543.);
            },
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    fn var_init() {
        let var_init = "var compound = 12;";
        //assert_eq!(ast_parser::var_init(var_init).unwrap(), String::from("compound"));
        match ast_parser::statement(var_init).unwrap() {
            StatementRet::VarLiteralAndId((id, Literal::Number(number_literal))) => {
                assert_eq!(id, String::from("compound"));
                assert_eq!(number_literal, 12.);
            }
            _ => panic!("Not a string, but better a number!"),
        }
    }

    #[test]
    fn class() {
        let class_def = 
        "class Heya {
            var init = 12;
            var lol = \"hey\";
            var empty;
        }";

        match ast_parser::class(class_def).unwrap() {
            (id, statements) => {
                assert_eq!(id, String::from("Heya"));
                assert_eq!(statements, vec![
                    StatementRet::VarLiteralAndId(("init".to_string(), Literal::Number(12.0))),
                    StatementRet::VarLiteralAndId(("lol".to_string(), Literal::String("hey".to_string()))),
                    StatementRet::VarIdOnly("empty".to_string())
                ]);
            },
        }
    }
}
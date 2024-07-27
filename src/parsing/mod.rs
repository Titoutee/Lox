use peg;
pub mod expression;
pub use expression::{Identifier, Literal, BinOp, Expression, MonOp};

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum Statement {
    VarDeclare(String),
    VarAssign(String, Expression),

    While {
        condition: Expression,
        body: Vec<Statement>,
    },
    
    IfThenElse {
        condition: Expression,
        if_branch: Vec<Statement>,
        else_branch: Option<Vec<Statement>>,
    },

    TopLevelConstruct(TopLevelConstruct),
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum TopLevelConstruct {
    Class(String, Vec<Statement>),
    Function(String, Vec<String>, Vec<Statement>),
}

pub enum ParseResult {
    Expression(Expression),
}

peg::parser! {
    pub grammar ast_parser() for str {
        rule _ = quiet!{[' ' | '\n' | '\t']*}

        rule identifier() -> Identifier
            = _ s:$((['a'..='z' | 'A'..='Z' | '_'])+) _ {s.to_owned()}

        rule literal_string() -> Literal
            = "\"" s:identifier() "\"" {Literal::String(s.to_owned())}

        rule literal_number() -> Literal // Only scalar type in Lox is f64
            = n:$(['0'..='9']+ ("." ['0'..='9']*)?) {?
                let inner = {n.parse::<f64>().or(Err("f64"))?};
                Ok(Literal::Number(inner))
            }
            
        rule literal_bool() -> Literal
            = s:identifier() {?
                match s.as_str() {
                    "True" => Ok(Literal::Bool(true)),
                    "False" => Ok(Literal::Bool(false)),
                    _ => Err("bool"),
                }
            }

        pub(super) rule literal() -> Literal
            = literal_number() / literal_string() / literal_bool()

        // Statements
        pub(super) rule var_declare() -> Identifier
            = "var" _ s:identifier() _ {s}

        pub(super) rule var_init() -> (Identifier, Expression)
            = d:var_declare() _ "=" _ e:expression() _ {(d, e)}

        // Used for functions and classes inner statements parsing
        rule inner_statements() -> Vec<Statement>
            = _ s:statement() ** _ {s}

        rule param_and_args() -> Vec<String>
            = s:$(identifier()+) ** (_ "," _) {s.into_iter().map(|slice| slice.to_owned()).collect()}

        pub(super) rule class() -> (Identifier, Vec<Statement>, Option<Identifier>)
            = "class" _ c:identifier() p:(_ "<" _ p:identifier() {p})? _ "{" _ stmts:inner_statements() _ "}" {(c.to_owned(), stmts, p)}

        pub(super) rule function_def() -> (Identifier, Vec<String>, Vec<Statement>)
            = "fun" _ f:identifier() "(" a:param_and_args() ")" _ "{" _ stmts:inner_statements() _ "}" {(f.to_owned(), a, stmts)}
        
        pub(super) rule while_() -> (Expression, Vec<Statement>)
            = "while" _ "(" _ e:expression() _ ")" _ "{" _ s:inner_statements() _ "}" {(e, s)}
        
        pub(super) rule if_then_else() -> (Expression, Vec<Statement>, Option<Vec<Statement>>) // "condition";"ifStmts";"elseStatements"
            = "if" _ "(" _ e:expression() _ ")" _ "{" _ i_s:inner_statements() _ "}" _ "else" _ "{" _ e_s:inner_statements() _ "}" {(e, i_s, Some(e_s))}

        pub(super) rule function_call() -> (Identifier, Vec<String>)
            = i:identifier() "(" a:param_and_args() ")" {(i.to_owned(), a)}
        
        // Core
        pub(super) rule expression() -> Expression
                = precedence! {
                x:(@) _ "==" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Eq }}
                x:(@) _ ">=" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Ge }}
                x:(@) _ "<=" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Le }}
                x:(@) _ ">" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Gt }}
                x:(@) _ "<" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Lt }}
                x:(@) _ "||" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Or }}
                x:(@) _ "&&" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::And }}
                x:(@) _ "//" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::XOr }}
                --
                x:(@) _ "+" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Plus }}
                x:(@) _ "-" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Minus }}
                --
                x:(@) _ "*" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Mul }}
                x:(@) _ "/" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Div }}
                --
                "-" _ y:@ {Expression::UnaryOp { operation: MonOp::Minus, operand: Box::new(y) }}
                "!" _ y:@ {Expression::UnaryOp { operation: MonOp::Not, operand: Box::new(y) }}
                --
                "(" _ e:expression() _ ")" { e }
                i:identifier() "(" args:expression() ** (_ "," _) ")" { Expression::FunctionCall { function_name: i, arguments: args } }
                //i:identifier() { Expression::Object { class_name: i.to_owned() }}
                i:identifier() "." f:identifier() { Expression::ObjectField { class_name: i.to_owned(), field: f.to_owned() }}
                // Atoms = max precedence level
                l:literal() { Expression::Literal(l) }
                i:identifier() { Expression::Var(i) }
            }

        pub(super) rule statement() -> Statement
            = i:var_init() ";" { Statement::VarAssign(i.0, i.1) }
              / e:var_declare() ";" { Statement::VarDeclare(e) }
              / c:class() { Statement::TopLevelConstruct(TopLevelConstruct::Class(c.0, c.1))}
              / f:function_def() { Statement::TopLevelConstruct(TopLevelConstruct::Function(f.0, f.1, f.2))}
              / w:while_() { Statement::While { condition: w.0, body: w.1 }}
              / i:if_then_else() { Statement::IfThenElse { condition: i.0, if_branch: i.1, else_branch: i.2 }}
        
        pub rule parse() -> Vec<Statement>
            = _ stmts:statement() ** _ {stmts}
    }
}

#[cfg(test)]
mod tests {
    use super::{Expression, Literal};
    use crate::parsing::{ast_parser, BinOp, MonOp, Statement};

    #[test]
    fn var_empty() {
        let var_empty = "var compound;";
        match ast_parser::statement(var_empty).unwrap() {
            Statement::VarDeclare(id) => {
                assert_eq!(id, String::from("compound"));
            }
            _ => panic!("Uninit should not contain a literal!"),
        }
    }

    #[test]
    fn var_empty_ill() {
        let var_empty = "var compound ;";
        match ast_parser::statement(var_empty).unwrap() {
            Statement::VarDeclare(id) => {
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
            Statement::VarDeclare(id) => {
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
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    fn literal_number() {
        let number = "6543";
        match ast_parser::literal(number).unwrap() {
            Literal::Number(n) => {
                assert_eq!(n, 6543.);
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    fn literal_bool() {
        let bool_1 = "True";
        let bool_2 = "False";
        //let bad_bool = "jhkjhdf";
        match ast_parser::literal(bool_1).unwrap() {
            Literal::Bool(n) => {
                assert_eq!(n, true);
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
        match ast_parser::literal(bool_2).unwrap() {
            Literal::Bool(n) => {
                assert_eq!(n, false);
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    #[should_panic]
    fn literal_bool_bad() {
        let bool = "sdkjfsdf";
        //let bad_bool = "jhkjhdf";
        match ast_parser::literal(bool).unwrap() {
            Literal::Bool(n) => {
                assert_eq!(n, true);
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    fn var_init() {
        let var_init = "var compound = 12;";
        //assert_eq!(ast_parser::var_init(var_init).unwrap(), String::from("compound"));
        match ast_parser::statement(var_init).unwrap() {
            Statement::VarAssign(id, Expression::Literal(Literal::Number(number_literal)) ) => {
                assert_eq!(id, String::from("compound"));
                assert_eq!(number_literal, 12.);
            }
            _ => panic!("Not a string, but better a number!"),
        }
    }

    #[test]
    fn var_init_bool_true() {
        let var_init = "var compound = True;";
        //assert_eq!(ast_parser::var_init(var_init).unwrap(), String::from("compound"));
        match ast_parser::statement(var_init).unwrap() {
            Statement::VarAssign(id, Expression::Literal(Literal::Bool(b)) ) => {
                assert_eq!(id, String::from("compound"));
                assert_eq!(b, true);
            }
            _ => panic!("Not a var assign"),
        }
    }

    #[test]
    fn var_init_bool_false() {
        let var_init = "var compound = False;";
        //assert_eq!(ast_parser::var_init(var_init).unwrap(), String::from("compound"));
        match ast_parser::statement(var_init).unwrap() {
            Statement::VarAssign(id, Expression::Literal(Literal::Bool(b)) ) => {
                assert_eq!(id, String::from("compound"));
                assert_eq!(b, false);
            }
            _ => panic!("Not a var assign"),
        }
    }

    #[test]
    fn class() {
        let class_def = "class Heya {
            var init = 12;
            var lol = \"hey\";
            var empty;
        }";

        match ast_parser::class(class_def).unwrap() {
            (id, statements, parent) => {
                assert_eq!(id, String::from("Heya"));
                assert_eq!(
                    statements,
                    vec![
                        Statement::VarAssign("init".to_string(), Expression::Literal(Literal::Number(12.0))),
                        Statement::VarAssign(
                            "lol".to_string(),
                            Expression::Literal(Literal::String("hey".to_string()
                        ))),
                        Statement::VarDeclare("empty".to_string())
                    ]
                );
                assert_eq!(parent, None)
            }
        }
    }

    #[test]
    fn class_inherit() {
        let class_def = "class Heya < OtherClass {
            var init = 12;
            var lol = \"hey\";
            var empty;
        }";

        match ast_parser::class(class_def).unwrap() {
            (id, statements, parent) => {
                assert_eq!(id, String::from("Heya"));
                assert_eq!(
                    statements,
                    vec![
                        Statement::VarAssign("init".to_string(), Expression::Literal(Literal::Number(12.0))),
                        Statement::VarAssign(
                            "lol".to_string(),
                            Expression::Literal(Literal::String("hey".to_string()
                        ))),
                        Statement::VarDeclare("empty".to_string())
                    ]
                );
                assert_eq!(parent, Some(String::from("OtherClass")));
            }
        }
    }

    #[test]
    fn function() {
        let fun_def = "fun Heya(hey) {
            var init = 12;
            var lol = \"hey\";
            var empty;
        }";

        match ast_parser::function_def(fun_def).unwrap() {
            (id, parameters, statements) => {
                assert_eq!(id, String::from("Heya"));
                assert_eq!(parameters, vec![String::from("hey")]);
                assert_eq!(
                    statements,
                    vec![
                        Statement::VarAssign("init".to_string(), Expression::Literal(Literal::Number(12.0))),
                        Statement::VarAssign(
                            "lol".to_string(),
                            Expression::Literal(Literal::String("hey".to_string())
                        )),
                        Statement::VarDeclare("empty".to_string())
                    ]
                );
            }
        }
    }

    #[test]
    fn function_call() {
        let fun_call = "my_func(heya, boo)";

        match ast_parser::function_call(fun_call).unwrap() {
            (id, parameters) => {
                assert_eq!(id, String::from("my_func"));
                assert_eq!(parameters, vec![String::from("heya"), String::from("boo")]);
            }
        }
    }

    #[test]
    #[should_panic]
    fn function_call_bad() {
        let fun_call = "my_ func(heya, boo)";

        match ast_parser::function_call(fun_call).unwrap() {
            (id, parameters) => {
                assert_eq!(id, String::from("my_func"));
                assert_eq!(parameters, vec![String::from("heya"), String::from("boo")]);
            }
        }
    }

    #[test]
    fn expression_1() {
        let expr = "1+2";
        let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs, rhs, operator: crate::parsing::BinOp::Plus })
    }

    #[test]
    fn expression_2() {
        let expr = "1*2";
        let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs, rhs, operator: crate::parsing::BinOp::Mul })
    }

    #[test]
    fn expression_3() {
        let expr = "1/2";
        let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs, rhs, operator: crate::parsing::BinOp::Div })
    }

    // Unary ops tests
    #[test]
    fn expression_4() {
        let expr = "-2";
        //let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::UnaryOp { operation: MonOp::Minus, operand: rhs })
    }

    #[test]
    fn expression_5() { // !(Literal::Number) should not work normally, but here parsing only is tested
        let expr = "!2";
        //let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::UnaryOp { operation: MonOp::Not, operand: rhs })
    }

    // Precedence tests
    #[test]
    fn expression_6() {
        let expr = "1+2*3";
        let op_1: Box<Expression> = Box::new(Expression::Literal(Literal::Number(1.)));
        let op_2 = Box::new(Expression::Literal(Literal::Number(2.)));
        let op_3 = Box::new(Expression::Literal(Literal::Number(3.)));
        
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs: op_1, rhs: Box::new(Expression::BinOperation { lhs: op_2, rhs: op_3, operator: BinOp::Mul }), operator: crate::parsing::BinOp::Plus })
    }
    
    #[test]
    fn expression_7() {
        let expr = "(1+2)*3";
        let op_1: Box<Expression> = Box::new(Expression::Literal(Literal::Number(1.)));
        let op_2 = Box::new(Expression::Literal(Literal::Number(2.)));
        let op_3 = Box::new(Expression::Literal(Literal::Number(3.)));
        
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs: Box::new(Expression::BinOperation { lhs: op_1, rhs: op_2, operator: BinOp::Plus }), rhs: op_3, operator: crate::parsing::BinOp::Mul })
    }

    #[test]
    fn expression_8() {
        let expr = "(1+2*3)*3";
        let op_1: Box<Expression> = Box::new(Expression::Literal(Literal::Number(1.)));
        let op_2 = Box::new(Expression::Literal(Literal::Number(2.)));
        let op_3 = Box::new(Expression::Literal(Literal::Number(3.)));
        let op_4 = Box::new(Expression::Literal(Literal::Number(3.)));
        
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs: Box::new(Expression::BinOperation { lhs: op_1, rhs: Box::new(Expression::BinOperation { lhs: op_2, rhs: op_3, operator: BinOp::Mul }), operator: BinOp::Plus }), rhs: op_4, operator: crate::parsing::BinOp::Mul })
    }

    // Variable integration tests
    #[test]
    fn expression_9() {
        let expr = "a+2";
        let op_1: Box<Expression> = Box::new(Expression::Var(String::from("a")));
        let op_2 = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs: op_1, rhs: op_2, operator: BinOp::Plus })
    }

    #[test]
    fn expression_11() {
        let expr = "a";
        //let op_1: Box<Expression> = Box::new(Expression::Var(String::from("a")));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(),  Expression::Var(String::from("a")));
    }

    // Function calls and object building
    #[test]
    fn expression_10() {
        let expr = "hey(4, a)";
        let op_1: Expression = Expression::FunctionCall { function_name: String::from("hey"), arguments: vec![Expression::Literal(Literal::Number(4.)), Expression::Var(String::from("a"))] };
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), op_1)
    }
}

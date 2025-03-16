use miette::{IntoDiagnostic, NamedSource, Result};

mod error;
mod lexer;

const SOURCE: &str = r#"
int main(void)
{
    const char *string = "abcde312$#@";
    const char *invalid = "*$#";
 
    size_t valid_len = strcspn(string, invalid);
    if(valid_len != strlen(string))
       printf("'%s' contains invalid chars starting at position %zu\n",
               string, valid_len);
}
"#;

fn main() -> Result<()> {
    let token_stream = lexer::lex(SOURCE)
        .into_diagnostic()
        .map_err(|error| error.with_source_code(NamedSource::new("dummy.c", SOURCE)))?;

    println!("{}", token_stream);

    Ok(())
}

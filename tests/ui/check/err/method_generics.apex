// expect: generic parameters are not supported
trait T { fn map<B>(&self, b: B) -> B; }

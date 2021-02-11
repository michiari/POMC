var foo;

pA() {
  foo = true;
  try {
    pB();
  } catch {
    pC();
  }
}

pB() {
  if (foo) {
    throw;
  } else {}
}

pC() { }

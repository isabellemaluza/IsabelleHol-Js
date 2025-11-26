function soma(a, b) {
  return a + b;
}
function provaComutatividade(n1, n2) {

  if (!Number.isInteger(n1) || !Number.isInteger(n2)) {
    return null;  
  }
  const esquerda = soma(n1, n2);
  const direita = soma(n2, n1);

  return esquerda === direita;
}

console.log(provaComutatividade(3, 7));  
console.log(provaComutatividade(10, 2));  
console.log(provaComutatividade(3.5, 7)); 
console.log(provaComutatividade("5", 7)); 

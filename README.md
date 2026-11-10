# Что это?

Реализация [toy_comp](https://github.com/true-grue/toy_comp) на idris2

Интерпретаторы для ISA:
- Память-память
- Стэковая
- Регистровая

И компиляторы для них

## Юзадж

```
pack build
# or for example
pack run toy_comp_idris2.ipkg  -m memory -i asm/fib_mem.asm
```  

## Отличия

В ассемблере:
- `OUT` печатает ASCII-символ без добавления новой строки
- `OUTN` печатает десятичное число с новой строкой

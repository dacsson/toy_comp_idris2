# Что это?

Реализация [toy_comp](https://github.com/true-grue/toy_comp) на idris2

Build with `pack build`, then run execution tests with `python3 test/test_memory.py`.
Интерпретаторы для ISA:
- Память-память
- Стэковая
- Регистровая

И компиляторы для них

## Отличия

В ассемблере:
- `OUT` печатает ASCII-символ без добавления новой строки
- `OUTN` печатает десятичное число с новой строкой

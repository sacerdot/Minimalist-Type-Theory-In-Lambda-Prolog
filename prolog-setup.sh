
FOLDER=$(pwd)

git clone https://github.com/teyjus/teyjus/  

git clone git@github.com:KiriaKasis/Lambda-Prolog.git

apt install aspcud opam ocaml omake flex bison -y

opam init

eval `opam config env`

opam switch 4.01.0

eval `opam config env`

apt remove ocaml -y


cd teyjus

omake all

cp tj* ~/.local/bin

cd ..

cd Lambda-Prolog





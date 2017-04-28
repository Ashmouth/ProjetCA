#include <Function.h>
#include <algorithm>
#include <iostream>
#include <list>
#include <string>

Function::Function() {
  _head = NULL;
  _end = NULL;
  BB_computed = false;
  BB_pred_succ = false;
  dom_computed = false;
}

Function::~Function() {}

void Function::set_head(Line *head) { _head = head; }

void Function::set_end(Line *end) { _end = end; }

Line *Function::get_head() { return _head; }

Basic_block *Function::get_firstBB() { return _myBB.front(); }

Line *Function::get_end() { return _end; }
void Function::display() {
  cout << "Begin Function" << endl;
  Line *element = _head;

  if (element == _end)
    cout << _head->get_content() << endl;

  while (element != _end) {
    cout << element->get_content() << endl;

    if (element->get_next() == _end) {
      cout << element->get_next()->get_content() << endl;
      break;
    } else
      element = element->get_next();
  }
  cout << "End Function\n\n" << endl;
}

int Function::size() {
  Line *element = _head;
  int lenght = 0;
  while (element != _end) {
    lenght++;
    if (element->get_next() == _end)
      break;
    else
      element = element->get_next();
  }
  return lenght;
}

void Function::restitution(string const filename) {

  Line *element = _head;
  ofstream monflux(filename.c_str(), ios::app);

  if (monflux) {
    monflux << "Begin" << endl;
    if (element == _end)
      monflux << _head->get_content() << endl;
    while (element != _end) {
      if (element->isInst() || element->isDirective())
        monflux << "\t";

      monflux << element->get_content();

      if (element->get_content().compare("nop"))
        monflux << endl;

      if (element->get_next() == _end) {
        if (element->get_next()->isInst() || element->get_next()->isDirective())
          monflux << "\t";
        monflux << element->get_next()->get_content() << endl;
        break;
      } else
        element = element->get_next();
    }
    monflux << "End\n\n" << endl;

  }

  else {
    cout << "Error cannot open the file" << endl;
  }

  monflux.close();
}

void Function::comput_label() {
  Line *element = _head;

  if (element == _end && element->isLabel())
    _list_lab.push_back(getLabel(element));
  while (element != _end) {

    if (element->isLabel())
      _list_lab.push_back(getLabel(element));

    if (element->get_next() == _end) {
      if (element->isLabel())
        _list_lab.push_back(getLabel(element));
      break;
    } else
      element = element->get_next();
  }
}

int Function::nbr_label() { return _list_lab.size(); }

Label *Function::get_label(int index) {

  list<Label *>::iterator it;
  it = _list_lab.begin();

  int size = (int)_list_lab.size();
  if (index < size) {
    for (int i = 0; i < index; i++)
      it++;
    return *it;
  } else
    cout << "Error get_label : index is bigger than the size of the list"
      << endl;

  return _list_lab.back();
}

Basic_block *Function::find_label_BB(OPLabel *label) {
  // Basic_block *BB = new Basic_block();
  int size = (int)_myBB.size();
  string str;
  for (int i = 0; i < size; i++) {
    if (get_BB(i)->is_labeled()) {

      str = get_BB(i)->get_head()->get_content();
      if (!str.compare(0, (str.size() - 1), label->get_op())) {
        return get_BB(i);
      }
    }
  }
  return NULL;
}

/* ajoute nouveau BB à la liste de BB de la fonction en le creant */

void Function::add_BB(Line *debut, Line *fin, Line *br, int index) {
  Basic_block *b = new Basic_block();
  b->set_head(debut);
  b->set_end(fin);
  b->set_index(index);
  b->set_branch(br);
  _myBB.push_back(b);
}

// Calcule la liste des blocs de base : il faut d�limiter les BB, en parcourant
// la liste des lignes/instructions � partir de la premiere, il faut s'arreter �
// chaque branchement (et prendre en compte le delayed slot qui appartient au
// meme BB, c'est l'instruction qui suit tout branchement) ou � chaque label (on
// estime que tout label est utilis� par un saut et donc correspond bien � une
// entete de BB).

/*
   void Function::comput_basic_block() {
   Line *debut, *current, *prev;
   bool verbose = true;
   current = _head;
   debut = NULL;
   prev = NULL;
   int ind = 0;
   string str;
   Line *l = NULL;
   Instruction *i = NULL;
   Line *b;

   cout << "comput BB" << endl;
   if (verbose) {
   cout << "head :" << _head->get_content() << endl;
   cout << "tail :" << _end->get_content() << endl;
   }
   if (BB_computed)
   return; // NE PAS TOUCHER

   while (current != _end) {

   if(current->isLabel()) {
   if (debut == NULL) {
   debut = current;
   } else {
   add_BB(debut, current->get_prev(), NULL, ind);
   debut = current;
   ind++;
   }
   }
   if(current->isInst()) {
   if (debut == NULL) {
   debut = current;
   }
   i = getInst(current);

   if (i->is_branch()) {
   add_BB(debut, current->get_next(), current, ind);
   current = current->get_next();
   debut = NULL;
   ind++;
   }
   prev = current;
   }
   current = current->get_next();
   }

   if(debut != NULL) {
   cout << "basic_block.debut != null" << endl;
   add_BB(debut, prev, NULL, ind);
   }

   if (verbose)
   cout << "end comput Basic Block" << endl;

   BB_computed = true;
   return;
   }
   */

void Function::comput_basic_block(){
  Line *debut, *current, *prev;
  bool verbose = true;
  current=_head;
  debut= NULL;
  prev = NULL;
  int ind=0;
  string str;
  Line *l=NULL;
  Instruction *i=NULL;
  Line * b;



  cout<< "comput BB" <<endl;
  if (verbose){
    cout<<"head :"<<_head->get_content()<<endl;
    cout<<"tail :"<<_end->get_content()<<endl;
  }
  if (BB_computed) return; // NE PAS TOUCHER

  while(current != _end){

    if(current->isLabel())
    {

      if(debut != NULL && prev == NULL)
      {

        add_BB(debut, current->get_prev(), NULL, ind);
        cout << "label .................................................." << endl;
        debut = current;
        ind++;


      }
      else
      {
        debut = current;

      }


    }
    else
      if(current->isInst())
      {

        i = getInst(current);

        //verifier si la ligne est une entete

        if(current->isInst())
        {
          if(i -> is_branch())
          {
            prev = current;
            current = current->get_next();
            add_BB(debut,current,prev, ind);

            ind ++;

            if(current->get_next()->isInst())
              debut = current->get_next();
          }
        }

      }
    current = current->get_next();
  }


  prev = current->get_prev()->get_prev();
  if(prev->isInst() && !getInst(prev)->is_branch())
  {
    add_BB(debut, prev->get_next(), NULL, ind);
  }

  if (verbose)
    cout<<"end comput Basic Block"<<endl;

  BB_computed = true;
  return;
}

int Function::nbr_BB() { return _myBB.size(); }

Basic_block *Function::get_BB(int index) {

  list<Basic_block *>::iterator it;
  it = _myBB.begin();
  int size = (int)_myBB.size();

  if (index < size) {
    for (int i = 0; i < index; i++)
      it++;
    return *it;
  } else
    return NULL;
}

list<Basic_block *>::iterator Function::bb_list_begin() {
  return _myBB.begin();
}

list<Basic_block *>::iterator Function::bb_list_end() { return _myBB.end(); }

/* comput_pred_succ calcule les successeurs et prédécesseur des BB, pour cela il
 * faut commencer par les successeurs */
/* et itérer sur tous les BB d'une fonction */
/* il faut determiner si un BB a un ou deux successeurs : dépend de la présence
 * d'un saut présent ou non à la fin */
/* pas de saut ou saut incontionnel ou appel de fonction : 1 successeur (lequel
 * ?)*/
/* branchement conditionnel : 2 successeurs */
/* le dernier bloc n'a pas de successeurs - celui qui se termine par jr R31 */
/* les sauts indirects n'ont pas de successeur */

/*
   void Function::comput_succ_pred_BB() {

   list<Basic_block *>::iterator it, it2;
   Basic_block *current;
   Instruction *instr;
   Basic_block *succ = NULL;
   Line *line = NULL;
   if (BB_pred_succ)
   return;

// A REMPLIR TODO
//for (it = bb_list_begin(); it != bb_list_end(); it++) {
//current = *it;
for (int index = 0; (current = get_BB(index)); index++) {
cout << index << endl;

line = current->get_branch();
cout << "Pass line" << endl;

if (line != NULL) {
cout << line->to_string() << endl;
instr = getInst(line);
cout << "Pass getInst" << endl;

//TODO: debug here
if (instr->is_indirect_branch()) {
// Add next block
cout << "Pass startind" << endl;
current->set_link_succ_pred(get_BB(index+1));
cout << "Pass endind" << endl;
}
if (instr->is_call()) {
// Add next block
cout << "Pass startcall" << endl;
current->set_link_succ_pred(get_BB(index+1));
cout << "Pass endcall" << endl;

} else if (instr->is_cond_branch()) {
// Add branch block and rest
cout << "Pass startbranch" << endl;
succ = find_label_BB(instr->get_op_label());
cout << "Pass find_label" << endl;
current->set_link_succ_pred(succ);
current->set_link_succ_pred(get_BB(index+1));
cout << "Pass endbranch" << endl;
}
}
cout << "Pass loop" << endl;
}
// ne pas toucher ci-dessous
BB_pred_succ = true;
return;
}
*/

void Function::comput_succ_pred_BB() {

  list<Basic_block*>::iterator it, it2;
  Basic_block *current;
  Instruction *instr;
  Basic_block *succ=NULL;
  if (BB_pred_succ) return;



  // A REMPLIR TODO
  //parcourir tous les blocs de base
  //for(it = bb_list_begin(); it != bb_list_end(); it++) {
  for (int index = 0; (current = get_BB(index)); index++) {
    //current = *it;
      
    // recupere la line qui contient le branchement
cout << "LOOP ................................ " << endl;
    if(current->get_branch()) {
      cout << "PASS ................................ " << endl;
      instr = getInst(current->get_branch());
      // recuperer le label de branchement si le branchement exist
      succ = get_BB(index+1);
      //succ =  *it++;


      if(instr->is_call()) {
        // ajouter le predecesseur de succ
        //succ = *it ++;
        succ = get_BB(index+1);
        current->set_link_succ_pred(succ);



      } else if(instr->is_cond_branch()) {
        // rendre le bloc de base sur le quel cette function methode est appelée

        succ = find_label_BB(instr->get_op_label());
        
        
        
        // si la condition est verifier ajouter le predecesseur de succ
        if(succ != NULL) {
          current->set_link_succ_pred(succ);
        }
        //sinon ajouter le bloc suivant
        //succ = *it++;
        succ = get_BB(index+1);
        current->set_link_succ_pred(succ);
      }
      
      
      
    // si y a pas de branchement, ajouter le bloc suivant
    } else if (get_BB(index+1)) {
    cout << "ENTER ................................ " << endl;
        current->set_link_succ_pred(get_BB(index+1));
    }
  }
  // ne pas toucher ci-dessous
  BB_pred_succ = true;
  return;
}


vector<bool> intersection(vector<bool> &v1, vector<bool> &v2) {
  vector<bool> v3;
  for(int i = 0; i < v1.size(); i++) {
    if(v1[i] && v2[i]) {
      v3.push_back(false);
    } else {
      v3.push_back(true);
    }
  }
  return v3;
}


void Function::compute_dom() {
  list<Basic_block *>::iterator it, it2;
  list<Basic_block *> workinglist;
  Basic_block *current, *bb, *pred;
  bool change = true;
  int size = _myBB.size();
  if (dom_computed)
    return;
  comput_succ_pred_BB();

  /* A REMPLIR */
  vector<bool> setT;
  vector<bool> setD;
  Basic_block *succ;
  workinglist.push_back(*(_myBB.begin()));      /* init list BB */

  while (workinglist.size() != 0) {
    change = false;
    current = workinglist.front();
    workinglist.pop_front();


    cout << "Comput_dom_PaSS.........................................." << endl;
    setT = {};
    int tmp = 0;
    int index = 0;
    int ibb = 0;
    
    for (int i = 0; i < size; i++) {  // TODO: check if T = N good
      if (current == get_BB(ibb)) {
        index = tmp;                  //Get index
      }
      bb = get_BB(ibb);
      setT.push_back(false);
      tmp++;
      ibb++;
    }
    cout << current->get_nb_succ() << endl;
    
    //TOP OK
    

    for (int i = 0; i < current->get_nb_pred(); i++) {
      pred = bb->get_predecessor(i);
      setT = intersection(setT, pred->Domin);
    }

    setD = setT;
    setD[index] = true; //Add himself

    if (setD != current->Domin) {   //TODO CHECK INFINITE LOOP
      cout << "Comput_dom_POUET.........................................." << endl;
      current->Domin = setD;
      change = true;
    }

    if (change) {
      for (int i = 0; i < current->get_nb_succ(); i++) {
        succ = current->get_successor1();
        //cout << succ->get_content() << endl;
        if(succ) {
        cout << "Comput_dom_Succ.........................................." << endl;
          workinglist.push_back(succ);
        }
        succ = current->get_successor2();
        if(succ) {
        cout << "Comput_dom_Succ2.........................................." << endl;
          workinglist.push_back(succ);
        }
      }
    }
  }

  // affichage du resultat
  it = _myBB.begin();

  for (int j = 0; j < size; j++) {
    current = *it;
    cout << "Dominants pour BB" << current->get_index() << " : ";
    for (int i = 0; i < nbr_BB(); i++) {
      if (current->Domin[i])
        cout << " BB" << i;
    }
    cout << endl;
    it++;
  }
  dom_computed = true;
  return;
}

void Function::compute_live_var() {
  list<Basic_block *>::iterator it, it2;
  list<Basic_block *> workinglist;
  Basic_block *current, *bb, *pred;
  bool change = true;
  int size = (int)_myBB.size();
  it = _myBB.begin();

  /* TODO A REMPLIR avec algo vu en cours et en TD*/
  /* algorithme itératif qui part des blocs sans successeur, ne pas oublier
   * que
   * lorsque l'on sort d'une fonction le registre $2 contient le résultat (il
   * est donc vivant), le registre pointeur de pile ($29) est aussi vivant !
   */

  //TODO: Do a loop in a bb and add $2 and $29
  /*
     it = _myBB.end();
     for(int i = size; i > 0; i--) {
     bb = *it;
  //LiveOut(bb) = U LiveIn(bb')
  if(i < size) {
  for(int j = 0; j < bb->get_nb_pred(); j++) {
  pred = bb->get_predecessor(j);
  for(int k = 0; k < NB_REG; k++) {
  bb->LiveOut[j] = LiveIn[j];
  }
  }
  }

  //LiveIn(bb) = use(bb) U (LiveOut(bb)\def(bb))
  for(int j = 0; j < NB_REG; j++) {
  boolean tmp = true;
  if(bb->LiveOut[j] == bb->DEF[j]) {
  tmp = false;
  }
  bb->LiveIn[j] = (bb->Use[j] || tmp);
  }

  //$i dead if LiveIn/Out(bb)
  //$i dead if LiveIn/Out(bb) but in bb

  it--;
  }
  */


  // Affichage du resultat
  it2 = _myBB.begin();
  for (int j = 0; j < size; j++) {
    bb = *it2;
    cout << "********* bb " << bb->get_index() << "***********" << endl;
    cout << "LIVE_OUT : ";
    for (int i = 0; i < NB_REG; i++) {
      if (bb->LiveOut[i]) {
        cout << "$" << i << " ";
      }
    }
    cout << endl;
    cout << "LIVE_IN :  ";
    for (int i = 0; i < NB_REG; i++) {
      if (bb->LiveIn[i]) {
        cout << "$" << i << " ";
      }
    }
    cout << endl;
    it2++;
  }
  return;
}

/* en implementant la fonction test de la classe BB, permet de tester des
 * choses
 * sur tous les blocs de base d'une fonction par exemple l'affichage de tous
 * les
 * BB d'une fonction ou l'affichage des succ/pred des BBs comme c'est le cas
 * --
 * voir la classe Basic_block et la méthode test */

void Function::test() {
  int size = (int)_myBB.size();
  for (int i = 0; i < size; i++) {
    get_BB(i)->test();
  }
  return;
}

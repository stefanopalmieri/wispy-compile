;; eliza.scm — Weizenbaum's ELIZA (1966), the original chatbot.
;;
;; Pattern-matching therapist, written in the language tradition
;; it helped start. Adapted for WispyScheme's R4RS.

;; ── String utilities ─────────────────────────────────────────

(define (char-alphabetic? c)
  (or (and (char>=? c #\a) (char<=? c #\z))
      (and (char>=? c #\A) (char<=? c #\Z))))

(define (char-downcase c)
  (if (and (char>=? c #\A) (char<=? c #\Z))
      (integer->char (+ (char->integer c) 32))
      c))

(define (string-downcase s)
  (list->string (map char-downcase (string->list s))))

;; Split a string into a list of lowercase words
(define (tokenize str)
  (let loop ((chars (string->list str)) (word '()) (words '()))
    (cond
      ((null? chars)
       (reverse (if (null? word)
                    words
                    (cons (list->string (reverse word)) words))))
      ((char-alphabetic? (car chars))
       (loop (cdr chars)
             (cons (char-downcase (car chars)) word)
             words))
      (else
       (loop (cdr chars)
             '()
             (if (null? word)
                 words
                 (cons (list->string (reverse word)) words)))))))

;; Check if pattern words appear at the start of a word list.
;; Returns (matched . tail) or #f.
(define (match-prefix pattern words)
  (cond
    ((null? pattern) (cons 1 words))
    ((null? words) #f)
    ((string=? (car pattern) (car words))
     (match-prefix (cdr pattern) (cdr words)))
    (else #f)))

;; Join words with spaces
(define (join-words lst)
  (if (null? lst)
      ""
      (let loop ((rest (cdr lst)) (result (car lst)))
        (if (null? rest)
            result
            (loop (cdr rest)
                  (string-append result " " (car rest)))))))

;; ── Reflection: swap pronouns ────────────────────────────────

(define *reflections*
  '(("i" "you") ("me" "you") ("my" "your") ("am" "are")
    ("you" "i") ("your" "my") ("are" "am")
    ("myself" "yourself") ("yourself" "myself")
    ("i'm" "you're") ("you're" "i'm")
    ("was" "were") ("were" "was")))

(define (reflect word)
  (let loop ((pairs *reflections*))
    (cond
      ((null? pairs) word)
      ((equal? word (car (car pairs))) (car (cdr (car pairs))))
      (else (loop (cdr pairs))))))

(define (reflect-words words)
  (map reflect words))

;; ── Pattern database ─────────────────────────────────────────
;; Each entry: (pattern-words . responses)
;; "*" in response means "insert reflected tail here"

(define *rules*
  (list
    (cons '("i" "need")
      '("Why do you need *?"
        "Would it really help you to get *?"
        "Are you sure you need *?"))
    (cons '("why" "don't" "you")
      '("Do you really think I don't *?"
        "Perhaps eventually I will *."
        "Do you really want me to *?"))
    (cons '("why" "can't" "i")
      '("Do you think you should be able to *?"
        "If you could *, what would you do?"
        "I don't know -- why can't you *?"))
    (cons '("i" "can't")
      '("How do you know you can't *?"
        "Perhaps you could * if you tried."
        "What would it take for you to *?"))
    (cons '("i" "am")
      '("Did you come to me because you are *?"
        "How long have you been *?"
        "How do you feel about being *?"))
    (cons '("i'm")
      '("How does being * make you feel?"
        "Do you enjoy being *?"
        "Why do you tell me you're *?"))
    (cons '("are" "you")
      '("Why does it matter whether I am *?"
        "Would you prefer it if I were not *?"
        "Perhaps you believe I am *."
        "I may be * -- what do you think?"))
    (cons '("what")
      '("Why do you ask?"
        "How would an answer to that help you?"
        "What do you think?"))
    (cons '("how")
      '("How do you suppose?"
        "Perhaps you can answer your own question."
        "What is it you're really asking?"))
    (cons '("because")
      '("Is that the real reason?"
        "What other reasons come to mind?"
        "Does that reason apply to anything else?"
        "If *, what else must be true?"))
    (cons '("sorry")
      '("There are many times when no apology is needed."
        "What feelings does apologizing bring up?"
        "Don't be sorry, be curious."))
    (cons '("hello")
      '("Hello. How are you feeling today?"
        "Hi there. What's on your mind?"
        "Hello. Tell me what's been troubling you."))
    (cons '("i" "think")
      '("Do you doubt *?"
        "Do you really think so?"
        "But you're not sure *?"))
    (cons '("friend")
      '("Tell me more about your friends."
        "When you think of a friend, what comes to mind?"
        "Why is this friend important to you?"))
    (cons '("yes")
      '("You seem quite sure."
        "OK, but can you elaborate a bit?"
        "I see. And what does that tell you?"))
    (cons '("no")
      '("Why not?"
        "You seem quite certain."
        "OK, tell me more about that."))
    (cons '("computer")
      '("Do computers worry you?"
        "What do you think about machines?"
        "Why do you mention computers?"
        "What do you think machines have to do with your problem?"))
    (cons '("i" "feel")
      '("Tell me more about those feelings."
        "Do you often feel *?"
        "When did you first feel *?"
        "What do you think is causing you to feel *?"))
    (cons '("i" "want")
      '("What would it mean if you got *?"
        "Why do you want *?"
        "What would you do if you got *?"
        "If you got *, then what would you do?"))
    (cons '("mother")
      '("Tell me more about your mother."
        "What was your relationship with your mother like?"
        "How does that make you feel about your mother?"
        "Good family relations are important."))
    (cons '("father")
      '("Tell me more about your father."
        "How did your father make you feel?"
        "How does that relate to your feelings today?"
        "Do you have trouble showing affection with your family?"))
    (cons '("dream")
      '("What does that dream suggest to you?"
        "Do you dream often?"
        "What persons appear in your dreams?"
        "Don't you think that dream has something to do with your problem?"))
    (cons '("maybe")
      '("You don't seem quite certain."
        "Why the uncertain tone?"
        "Can't you be more positive?"
        "You aren't sure?"))
    (cons '("always")
      '("Can you think of a specific example?"
        "When?"
        "What incident are you thinking of?"
        "Really -- always?"))))

(define *defaults*
  '("Very interesting. Tell me more."
    "I'm not sure I understand you fully."
    "Please go on."
    "What does that suggest to you?"
    "Do you have strong feelings about that?"
    "That is interesting. Please continue."
    "Tell me more about that."
    "Does talking about this bother you?"))

;; ── Response selection ────────────────────────────────────────

;; Simple rotating index per rule (uses list mutation via set-cdr!)
(define *counters* (map (lambda (r) (cons 0 0)) *rules*))
(define *default-counter* (cons 0 0))

(define (pick-rotating lst counter)
  (let* ((idx (car counter))
         (item (list-ref lst (remainder idx (length lst)))))
    (set-car! counter (+ idx 1))
    item))

;; Fill in "*" with the reflected tail
(define (fill-response template tail-str)
  (let* ((chars (string->list template))
         (len (length chars)))
    (let loop ((i 0) (result '()))
      (cond
        ((= i len)
         (list->string (reverse result)))
        ((char=? (list-ref chars i) #\*)
         (loop (+ i 1)
               (append (reverse (string->list tail-str)) result)))
        (else
         (loop (+ i 1) (cons (list-ref chars i) result)))))))

;; ── Main matching engine ─────────────────────────────────────

(define (respond words)
  (let loop ((rules *rules*) (counters *counters*))
    (if (null? rules)
        ;; No pattern matched — use default
        (pick-rotating *defaults* *default-counter*)
        ;; Try to match this rule's pattern anywhere in the input
        (let ((pattern (car (car rules)))
              (responses (cdr (car rules))))
          (let scan ((w words))
            (if (null? w)
                (loop (cdr rules) (cdr counters))
                (let ((result (match-prefix pattern w)))
                  (if result
                      (let* ((tail (cdr result))
                             (reflected (join-words (reflect-words tail)))
                             (template (pick-rotating responses (car counters))))
                        (fill-response template reflected))
                      (scan (cdr w))))))))))

;; ── Input ─────────────────────────────────────────────────────

;; Read a line from stdin using read-char
(define (get-line)
  (let loop ((chars '()))
    (let ((c (read-char)))
      (cond
        ((eof-object? c)
         (if (null? chars) c (list->string (reverse chars))))
        ((char=? c #\newline)
         (list->string (reverse chars)))
        (else
         (loop (cons c chars)))))))

;; ── REPL ─────────────────────────────────────────────────────

(define (eliza)
  (display "ELIZA: Hello. I am a psychotherapist.")
  (newline)
  (display "ELIZA: Tell me what's been on your mind.")
  (newline)
  (newline)
  (let loop ()
    (display "YOU:   ")
    (let ((input (get-line)))
      (cond
        ((eof-object? input)
         (newline)
         (display "ELIZA: Goodbye. It was nice talking to you.")
         (newline))
        ((member (string-downcase input) '("bye" "quit" "exit" ""))
         (display "ELIZA: Goodbye. It was nice talking to you.")
         (newline))
        (else
         (let ((words (tokenize input)))
           (display "ELIZA: ")
           (display (respond words))
           (newline)
           (newline)
           (loop)))))))

(eliza)
